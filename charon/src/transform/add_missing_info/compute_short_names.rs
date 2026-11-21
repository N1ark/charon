use indexmap::map::Entry;
use itertools::Itertools;
use rayon::prelude::*;

use crate::ast::*;

use crate::transform::{TransformCtx, ctx::TransformPass};

enum FoundName<'a> {
    Unique {
        long: &'a [PathElem],
        ids: Vec<ItemId>,
    },
    Multiple,
}

fn register_short_name_candidate<'a>(
    short_names: &mut ShortNames<'a>,
    short: PathElem,
    long: &'a [PathElem],
    id: ItemId,
) {
    match short_names.entry(short) {
        Entry::Occupied(mut e) => match e.get_mut() {
            FoundName::Unique {
                long: found_long,
                ids,
            } => {
                if *found_long == long {
                    ids.push(id)
                } else {
                    e.insert(FoundName::Multiple);
                }
            }
            FoundName::Multiple => {}
        },
        Entry::Vacant(e) => {
            e.insert(FoundName::Unique {
                long,
                ids: vec![id],
            });
        }
    }
}

/// Insertion-ordered so that the output doesn't depend on how `PathElem`s hash.
type ShortNames<'a> = SeqHashMap<PathElem, FoundName<'a>>;

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // We compute the candidates of each name in parallel, then register them in order.
        let names = ctx.translated.item_names.iter().collect_vec();
        let candidates = names
            .into_par_iter()
            .map(|(&id, name)| (id, name_candidates(&ctx.translated, name)))
            .collect::<Vec<_>>();

        let mut short_names_map = SeqHashMap::default();
        let mut short_names: ShortNames = Default::default();
        for (id, (trunc_name, candidate)) in candidates {
            if let Some(trunc_name) = trunc_name {
                short_names_map.insert(id, trunc_name);
            }
            if let Some((short, name_slice)) = candidate {
                register_short_name_candidate(&mut short_names, short, name_slice, id);
            }
        }

        let unique = short_names
            .into_iter()
            .filter_map(|(short, found)| match found {
                FoundName::Unique { ids, .. } => Some((short, ids)),
                FoundName::Multiple => None,
            })
            .flat_map(|(short, ids)| ids.into_iter().map(move |id| (id, short.clone())))
            .collect_vec();
        let item_names = &ctx.translated.item_names;
        let unique = unique
            .into_par_iter()
            .map(|(id, short)| {
                let mut short_name = Name { name: vec![short] };
                if let [.., mono @ PathElem::Instantiated(..)] = item_names[&id].name.as_slice() {
                    short_name.name.push(mono.clone());
                }
                (id, short_name)
            })
            .collect::<Vec<_>>();
        for (id, short_name) in unique {
            short_names_map.insert(id, short_name);
        }
        ctx.translated.short_names = short_names_map;
    }
}

/// The short name of an item that is inside a trait impl (truncated from the rightmost impl),
/// and the suffix that becomes its short name if it's the only one to end with it, with the part
/// of its name that must be unique for that.
fn name_candidates<'a>(
    krate: &TranslatedCrate,
    name: &'a Name,
) -> (Option<Name>, Option<(PathElem, &'a [PathElem])>) {
    let mut name_slice = name.name.as_slice();

    // Trait impls are sufficiently unique information, so truncate starting from the
    // rightmost impl.
    let mut trunc_name = None;
    if let Some((i, _)) = name_slice
        .iter()
        .enumerate()
        .rfind(|(_, elem)| matches!(elem, PathElem::Impl(ImplElem::Trait(..), ..)))
    {
        name_slice = &name.name[i..];
        trunc_name = Some(Name {
            name: name_slice.to_vec(),
        });
    }

    if let [prefix @ .., PathElem::Instantiated(..)] = name_slice {
        name_slice = prefix;
    }
    // Ignoring monomorphizations and disambiguators, if a name is the only one to end with
    // a given suffix, we accumulate the ids of all the items with that name (there may be
    // several thanks to monomorphizations).
    let candidate = match name_slice {
        [.., PathElem::Ident(ident, _)] => {
            Some(PathElem::Ident(ident.clone(), Disambiguator::ZERO))
        }
        // Tuples and `str` are excluded: those are types with a syntax of their own.
        [.., PathElem::Builtin(builtin, _)] if !builtin.is_tuple() && !builtin.is_str() => {
            Some(PathElem::Builtin(*builtin, Disambiguator::ZERO))
        }
        [PathElem::Impl(ImplElem::Trait(impl_id))]
            if let Some(trait_impl) = krate.trait_impls.get(*impl_id) =>
        {
            trait_impl_short_name(&krate.item_names, trait_impl)
                .map(|short| PathElem::Ident(short.into(), Disambiguator::ZERO))
        }

        _ => None,
    };
    (trunc_name, candidate.map(|short| (short, name_slice)))
}

fn trait_impl_short_name(
    item_names: &SeqHashMap<ItemId, Name>,
    trait_impl: &TraitImpl,
) -> Option<String> {
    fn args_to_idents(
        item_names: &SeqHashMap<ItemId, Name>,
        generics: &GenericArgs,
    ) -> Vec<String> {
        generics
            .types
            .iter()
            .filter_map(|t| ty_to_idents(item_names, t))
            .collect()
    }

    fn ty_to_idents(item_names: &SeqHashMap<ItemId, Name>, ty: &Ty) -> Option<String> {
        Some(match ty.kind() {
            TyKind::Scalar(scalar) => scalar.to_string(),
            TyKind::Slice(..) => "slice".to_owned(),
            TyKind::Array(..) => "array".to_owned(),
            TyKind::Adt(tref) => item_to_ident(item_names, ItemId::Type(tref.id))?,
            _ => return None,
        })
    }

    fn item_to_ident(item_names: &SeqHashMap<ItemId, Name>, id: ItemId) -> Option<String> {
        Some(item_names.get(&id)?.short_str()?.to_owned())
    }

    let trait_id = trait_impl.impl_trait.id;
    let (self_ty, partial_trait_ref) = trait_impl.impl_trait.split_self();
    let self_ty = self_ty.as_ref()?;

    let mut candidate = vec!["impl".to_owned()];
    if trait_impl.is_negative {
        candidate.push("not".to_owned());
    }
    candidate.push(item_to_ident(item_names, trait_id.into())?);
    candidate.extend(args_to_idents(item_names, &partial_trait_ref.generics));
    candidate.push("for".to_owned());
    candidate.push(if let TyKind::TypeVar(_) = self_ty.kind() {
        "T".to_string()
    } else {
        ty_to_idents(item_names, self_ty)?
    });
    if let TyKind::Adt(tref) = self_ty.kind() {
        candidate.extend(args_to_idents(item_names, &tref.generics));
    };
    Some(candidate.join("_"))
}
