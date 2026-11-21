//! Renaming of item and file ids while deserializing. This lets us load values serialized in
//! another translation session, where items and files got other ids.
use crate::ast::{FileId, ItemId};
use std::cell::Cell;

/// The ids to use instead of deserialized ones.
pub trait IdRemap {
    fn item_id(&self, id: ItemId) -> ItemId;
    fn file_id(&self, id: FileId) -> FileId;
}

thread_local! {
    static CURRENT: Cell<Option<&'static dyn IdRemap>> = const { Cell::new(None) };
}

/// Run `f`, renaming with `remap` the item and file ids that it deserializes on this thread.
pub fn with_id_remap<R>(remap: &dyn IdRemap, f: impl FnOnce() -> R) -> R {
    struct Restore(Option<&'static dyn IdRemap>);
    impl Drop for Restore {
        fn drop(&mut self) {
            CURRENT.set(self.0);
        }
    }
    // SAFETY: `remap` stays in the thread-local only until `Restore` puts back the previous value,
    // which happens before `remap` goes out of scope, even if `f` panics.
    let remap: &'static dyn IdRemap = unsafe { std::mem::transmute(remap) };
    let _restore = Restore(CURRENT.replace(Some(remap)));
    f()
}

pub(crate) fn remap_item_id<I: Into<ItemId> + TryFrom<ItemId>>(id: I) -> I {
    match CURRENT.get() {
        None => id,
        Some(remap) => remap
            .item_id(id.into())
            .try_into()
            .ok()
            .expect("an item id was remapped to an item of another kind"),
    }
}

pub(crate) fn remap_file_id(id: FileId) -> FileId {
    match CURRENT.get() {
        None => id,
        Some(remap) => remap.file_id(id),
    }
}
