//! Merge several crates of the same build into one, ensuring each translated crate's local items
//! are kept. Allows having many local crates, so that the MIR level is the same across crates (since
//! foreign crates otherwise always use elaborated MIR).
use std::collections::HashSet;

use crate::{ast::*, options::CliOpts};

use super::CrateData;
use super::merge;

/// Merge per-crate [`CrateData`]s into a single [`CrateData`] named `crate_name`.
pub fn merge(options: CliOpts, krates: Vec<CrateData>, crate_name: String) -> CrateData {
    let mut merged = merge::merge(options, krates, MultiCrate);
    merged.translated.crate_name = crate_name;
    merged
}

struct MultiCrate;

impl merge::MergeStrategy for MultiCrate {
    type Key = String;

    fn key(&self, krate: &TranslatedCrate) -> String {
        krate.crate_name.clone()
    }

    /// For each group, keep the local item if there is one, otherwise an arbitrary one.
    fn link(
        &mut self,
        krate: &mut TranslatedCrate,
        groups: Vec<SeqHashMap<String, ItemId>>,
    ) -> merge::Remapping {
        let mut remap = merge::Remapping::default();
        for group in groups {
            let is_local = |id: &ItemId| {
                krate
                    .get_item(*id)
                    .is_some_and(|item| item.item_meta().is_local)
            };
            let locals = group
                .iter()
                .filter(|(_, id)| is_local(id))
                .collect::<Vec<_>>();
            let kept = match *locals.as_slice() {
                [(_, &id)] => id,
                // no local version, take any version (ideally one that has an item)
                [] => group
                    .values()
                    .copied()
                    .min_by_key(|&id| krate.get_item(id).is_none())
                    .unwrap(),
                // Allocations are local to every crate that uses them: keep the version of the
                // crate their path starts with, if any.
                [(_, &first), ..] => {
                    let owner = match krate.item_name(first).name.first() {
                        Some(PathElem::Ident(name, _)) => Some(name),
                        _ => None,
                    };
                    locals
                        .iter()
                        .find(|(crate_name, _)| Some(*crate_name) == owner)
                        .map_or(first, |&(_, &id)| id)
                }
            };
            for &id in group.values() {
                remap.add_remapping(id, kept);
            }
        }
        for (&id, _) in &remap {
            krate.remove_item(id);
        }
        remap
    }

    /// Keep the items reachable from the start-from items of any of the crates: each crate's
    /// translation has all of its items, for the other crates to use.
    fn finish(&mut self, krate: &mut TranslatedCrate) {
        let mut reached: HashSet<ItemId> = krate
            .all_items_with_ids()
            .filter(|(_, item)| item.item_meta().started_from)
            .map(|(id, _)| id)
            .collect();
        let mut todo: Vec<ItemId> = reached.iter().copied().collect();
        while let Some(id) = todo.pop() {
            let mut refs = ItemIds::default();
            if let Some(item) = krate.get_item(id) {
                let _ = item.drive(&mut refs);
            }
            todo.extend(refs.0.into_iter().filter(|&id| reached.insert(id)));
        }
        for id in krate.all_ids() {
            if !reached.contains(&id) {
                krate.remove_item(id);
            }
        }
    }
}

/// The items an item refers to.
#[derive(Default, Visitor)]
struct ItemIds(Vec<ItemId>);

impl VisitAst for ItemIds {
    fn enter_type_decl_id(&mut self, id: &TypeDeclId) {
        self.0.push((*id).into());
    }
    fn enter_fun_decl_id(&mut self, id: &FunDeclId) {
        self.0.push((*id).into());
    }
    fn enter_global_decl_id(&mut self, id: &GlobalDeclId) {
        self.0.push((*id).into());
    }
    fn enter_trait_decl_id(&mut self, id: &TraitDeclId) {
        self.0.push((*id).into());
    }
    fn enter_trait_impl_id(&mut self, id: &TraitImplId) {
        self.0.push((*id).into());
    }
}
