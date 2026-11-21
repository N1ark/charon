use crate::ast::*;
use derive_generic_visitor::*;
use enum_as_inner::EnumAsInner;
use serde_state::{DeserializeState, SerializeState};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(EnumAsInner)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("R"))]
pub enum Region {
    /// Region variable. See `DeBruijnVar` for details.
    Var(RegionDbVar),
    /// The least upper bound, in the outlives ordering, of the regions in this type.
    /// `'lub<T>: 'a` is equivalent to `T: 'a`.
    Lub(Ty),
    /// Static region
    Static,
    /// Body-local region, considered existentially-bound at the level of a body.
    Body(RegionId),
    /// Erased region
    Erased,
}

/// Replace each body region `'i` in `x` with `f(i)`.
pub fn map_body_regions<T: AstVisitable>(x: &mut T, f: impl FnMut(RegionId) -> RegionId) {
    #[derive(Visitor)]
    struct MapBodyRegions<F>(F);
    impl<F: FnMut(RegionId) -> RegionId> VisitAstMut for MapBodyRegions<F> {
        fn visit_with_cached_type_info<T: AstVisitable + HashConsable>(
            &mut self,
            value: &mut HashConsed<WithCachedTypeInfo<T>>,
        ) -> ControlFlow<Self::Break> {
            if value.type_info().has_erased_or_body_regions() {
                self.visit_inner(value)
            } else {
                ControlFlow::Continue(())
            }
        }
        fn enter_region(&mut self, r: &mut Region) {
            if let Region::Body(id) = r {
                *id = (self.0)(*id);
            }
        }
    }
    let _ = MapBodyRegions(f).visit(x);
}
