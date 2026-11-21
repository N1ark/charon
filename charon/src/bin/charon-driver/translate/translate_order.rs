//! Making what we translate independent of the order in which we translate items.
//!
//! We may translate items in any order, e.g. in parallel. The ids of items and files depend on that
//! order, and we don't mind. A few things items contain would depend on it too, so we record them
//! and settle them once translation is done:
//! - the first lookup of an anonymous allocation decides at which type we view it: instead we pick
//!   the view by a rule, and translate again the items that saw another one;
//! - an impl would refer to its vtable if we translated the vtable before the impl: instead it
//!   refers to its vtable if we translated it at all, see `settle_vtables`;
//! - errors are reported at the end, sorted by location, which also lets the notes on errors in
//!   external items list all the places that use them.
use super::translate_ctx::*;
use crate::hax::BaseState;
use charon_lib::ast::*;
use charon_lib::errors::ErrorRecording;
use rustc_const_uneval::{AllocView, ViewLookup};
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use rustc_middle::mir::interpret::AllocId;

impl<'tcx> TranslateCtx<'tcx> {
    /// Start recording what translation does that depends on the order of translation, to settle
    /// it with `settle_translation_order` once translation is done.
    pub(crate) fn start_recording(&mut self) {
        self.errors.get_mut().recording = Some(ErrorRecording::default());
        self.hax_state.global_cache().alloc_types.record_lookups();
    }

    pub(crate) fn is_recording(&self) -> bool {
        self.errors.borrow().recording.is_some()
    }

    /// Run `f`, which translates the item `id`, recording the views it looks up.
    pub(crate) fn record_views_of(&mut self, id: ItemOrModuleId, f: impl FnOnce(&mut Self)) {
        if !self.is_recording() {
            return f(self);
        }
        let alloc_types = self.hax_state.global_cache().alloc_types.clone();
        // The lookups of an item we translate in the middle of another are not the other's.
        let outer = alloc_types.take_lookups();
        f(self);
        let lookups = alloc_types.take_lookups();
        alloc_types.put_back_lookups(outer);
        if let Some(id) = id.as_item()
            && !lookups.is_empty()
        {
            self.view_lookups.push((id, lookups));
        }
    }

    /// Settle what depends on the order of translation, see the module docs.
    pub(crate) fn settle_translation_order(&mut self) {
        if self.is_recording() {
            self.settle_views();
        }
        self.settle_vtables();
        if self.is_recording() {
            self.report_recorded_errors();
        }
    }

    /// An impl refers to the vtable it computed when we translated that vtable, else to a vtable we
    /// translated for it (a vtable can have several item sources, e.g. in mono mode), else it is
    /// lazy.
    fn settle_vtables(&mut self) {
        use charon_lib::formatter::IntoFormatter;
        use charon_lib::pretty::FmtWithCtx;
        let krate = &self.translated;
        let fmt = krate.into_fmt();
        // Between several vtables translated for an impl, pick one by a rule that doesn't depend
        // on the order.
        let mut translated: HashMap<TraitImplId, (String, GlobalDeclRef)> = HashMap::default();
        for (impl_id, vtable) in std::mem::take(&mut self.translated_vtables) {
            let key = vtable.with_ctx(&fmt).to_string();
            match translated.get(&impl_id) {
                Some((other, _)) if *other <= key => {}
                _ => {
                    translated.insert(impl_id, (key, vtable));
                }
            }
        }
        let settled: Vec<(TraitImplId, VTableDecl)> = krate
            .trait_impls
            .iter()
            .filter_map(|timpl| match &timpl.vtable {
                VTableDecl::VTable(vtable) if krate.global_decls.get(vtable.id).is_some() => None,
                VTableDecl::VTable(_) | VTableDecl::Lazy => {
                    let vtable = match translated.remove(&timpl.def_id) {
                        Some((_, vtable)) => VTableDecl::VTable(vtable),
                        None => VTableDecl::Lazy,
                    };
                    Some((timpl.def_id, vtable))
                }
                VTableDecl::NotDynCompatible | VTableDecl::Unknown(_) => None,
            })
            .collect();
        for (impl_id, vtable) in settled {
            self.translated.trait_impls[impl_id].vtable = vtable;
        }
    }

    /// Translate this item again, forgetting the errors it raised.
    pub(crate) fn translate_again(&mut self, id: ItemId) {
        self.translated.remove_item_temporarily(id);
        let errors = self.errors.get_mut();
        errors.forget_item_errors(id);
        if let Some(recording) = &mut errors.recording {
            let count = recording.errors.len();
            recording.errors.retain(|error| error.def_id != Some(id));
            let forgotten = count - recording.errors.len();
            recording.count -= forgotten;
            errors.error_count -= forgotten;
        }
        let src = self.reverse_id_map[&id].clone();
        self.translate_item(&src);
    }

    /// Translate what the queue holds, e.g. after translating items again.
    fn translate_queue(&mut self) {
        while let Some(src) = self.items_to_translate.pop_front() {
            if self.processed.insert(src.clone()) {
                self.translate_item(&src);
            }
            if let Some(request) = self.requested_bodies.remove(&src) {
                self.body_requests.discard(request);
            }
        }
    }

    /// View each allocation at the same type in every item, whatever the order of translation: at
    /// a type one of its lookups asks for if any, else untyped.
    fn settle_views(&mut self) {
        let alloc_types = self.hax_state.global_cache().alloc_types.clone();
        for round in 0.. {
            assert!(round < 10, "the views of allocations don't converge");
            // Typed views are better than untyped ones; between types we pick one by a rule that
            // doesn't depend on the order.
            let rank = |view: AllocView<'tcx>| match view {
                AllocView::Untyped => None,
                AllocView::Typed(ty) => Some(format!("{ty:?}")),
            };
            let mut views: HashMap<AllocId, (Option<String>, AllocView<'tcx>)> = HashMap::default();
            for lookup in self.view_lookups.iter().flat_map(|(_, lookups)| lookups) {
                let candidate = (rank(lookup.default), lookup.default);
                match views.get(&lookup.alloc_id) {
                    Some(view) if view.0 >= candidate.0 => {}
                    _ => {
                        views.insert(lookup.alloc_id, candidate);
                    }
                }
            }
            let sees_other_view =
                |lookup: &ViewLookup<'tcx>| views[&lookup.alloc_id].1 != lookup.view;
            let to_translate: HashSet<ItemId> = self
                .view_lookups
                .iter()
                .filter(|(_, lookups)| lookups.iter().any(sees_other_view))
                .map(|(id, _)| *id)
                .collect();
            if to_translate.is_empty() {
                break;
            }
            for (alloc_id, (_, view)) in views {
                alloc_types.force_view(alloc_id, view);
            }
            self.view_lookups
                .retain(|(id, _)| !to_translate.contains(id));
            for id in to_translate {
                self.translate_again(id);
            }
            self.translate_queue();
        }
        self.view_lookups = Default::default();
    }

    /// Report the errors recorded during translation, in the order of their locations.
    fn report_recorded_errors(&mut self) {
        let errors = self.errors.get_mut();
        let recording = errors.recording.take().unwrap();
        // We count them again as we report them.
        errors.error_count -= recording.count;
        errors.clear_items_with_errors();
        for (from, to) in recording.dep_edges {
            errors.insert_dep_edge(from, to);
        }
        let mut recorded = recording.errors;
        let files = &self.translated.files;
        recorded.sort_by_cached_key(|error| {
            let span = error.span.data();
            let file = files.get(span.file_id).map(|file| file.name.clone());
            (file, span.beg, span.end, error.msg.clone())
        });
        for error in recorded {
            errors.replay_error(&self.translated, error);
        }
        errors.def_id = None;
        errors.def_id_is_local = false;
    }
}
