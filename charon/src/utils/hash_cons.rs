use derive_generic_visitor::{Drive, DriveMut, DriveTwo, Visit, VisitMut, VisitTwo};
use std::hash::Hash;
use std::ops::{ControlFlow, Deref, DerefMut};

use crate::utils::type_map::Mappable;

/// Hash-consed data structure: a pointer to a value stored in a global interning table, which
/// guarantees that two equal values are stored at the same address. This makes it possible to
/// compare and hash by address. Interned values are never freed.
// Warning: a `derive` should not introduce a way to create a new `HashConsed` value without
// going through the interning table.
pub struct HashConsed<T>(std::ptr::NonNull<T>);

// SAFETY: this is semantically a `&'static T`.
unsafe impl<T: Sync> Send for HashConsed<T> {}
unsafe impl<T: Sync> Sync for HashConsed<T> {}

impl<T> Clone for HashConsed<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for HashConsed<T> {}

impl<T> PartialEq for HashConsed<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl<T> Eq for HashConsed<T> {}

impl<T> Hash for HashConsed<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<T> HashConsed<T> {
    pub fn inner(&self) -> &T {
        // SAFETY: interned values are never freed, see `intern_table::Table`.
        unsafe { self.0.as_ref() }
    }
}

impl<T: PartialOrd> PartialOrd for HashConsed<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.inner().partial_cmp(other.inner())
    }
}

impl<T: Ord> Ord for HashConsed<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.inner().cmp(other.inner())
    }
}

pub trait HashConsable: Hash + PartialEq + Eq + Clone + Mappable {}
impl<T> HashConsable for T where T: Hash + PartialEq + Eq + Clone + Mappable {}

// Private module that contains the static we'll use as interning map. A value of type
// `HashCons` MUST NOT be created in any other way than this table, else hashing and euqality
// on it will be broken. Note that this likely means that if a crate uses charon both as a
// direct dependency and as a dylib, then the static will be duplicated, causing hashing and
// equality on `HashCons` to be broken.
mod intern_table {
    use rustc_hash::FxBuildHasher;
    use std::sync::{LazyLock, RwLock};

    use super::{HashConsable, HashConsed};
    use crate::utils::type_map::{Mappable, Mapper, TypeMap};

    // This is a static mutable `HashSet<&'static T>` that records for each `T` value a unique
    // allocation that contains the same value. Values inside the set are hashed/compared as is
    // normal for `T`. Once we've gotten a reference out of the set however, we're sure that
    // "T-equality" implies address-equality.
    struct InternMapper;
    impl Mapper for InternMapper {
        type Value<T: Mappable> = Table<T>;
    }

    struct Table<T: 'static> {
        set: hashbrown::HashSet<&'static T, FxBuildHasher>,
        /// Storage for new values. Values are never freed, and this is never reallocated: when
        /// it's full we leak it and start a new one.
        chunk: Vec<T>,
    }
    impl<T> Default for Table<T> {
        fn default() -> Self {
            Self {
                set: Default::default(),
                chunk: Vec::new(),
            }
        }
    }
    impl<T> Table<T> {
        fn alloc(&mut self, value: T) -> &'static T {
            if self.chunk.len() == self.chunk.capacity() {
                let new_cap = (self.chunk.capacity() * 2).clamp(16, 1 << 14);
                std::mem::forget(std::mem::replace(
                    &mut self.chunk,
                    Vec::with_capacity(new_cap),
                ));
            }
            self.chunk.push(value);
            // SAFETY: the chunk is never reallocated nor dropped, so its elements live forever.
            unsafe { &*std::ptr::from_ref(self.chunk.last().unwrap()) }
        }
    }
    static INTERNED: LazyLock<RwLock<TypeMap<InternMapper>>> = LazyLock::new(Default::default);

    pub(super) fn intern<T: HashConsable>(inner: T) -> HashConsed<T> {
        // Fast read-only check.
        if let read_guard = INTERNED.read().unwrap()
            && let Some(table) = read_guard.get::<T>()
            && let Some(&interned) = table.set.get(&inner)
        {
            return HashConsed(interned.into());
        }
        // Concurrent access is possible right here, so we have to check everything again.
        let mut write_guard = INTERNED.write().unwrap();
        let table = write_guard.or_default::<T>();
        if let Some(&interned) = table.set.get(&inner) {
            HashConsed(interned.into())
        } else {
            let interned = table.alloc(inner);
            table.set.insert(interned);
            HashConsed(interned.into())
        }
    }
}

impl<T> HashConsed<T>
where
    T: HashConsable,
{
    /// Deduplicate the values by hashing them. This deduplication is crucial for the hashing
    /// function to be correct. This is the only function allowed to create `Self` values.
    pub fn new(inner: T) -> Self {
        intern_table::intern(inner)
    }

    /// Get a copy of the pointed-to value that can be mutated; the modified value is re-interned
    /// when the returned guard is dropped.
    pub fn as_mut(&mut self) -> impl DerefMut<Target = T> {
        struct HashConsedMutRef<'a, T: HashConsable> {
            hc: &'a mut HashConsed<T>,
            value: Option<T>,
        }
        impl<T: HashConsable> Deref for HashConsedMutRef<'_, T> {
            type Target = T;
            fn deref(&self) -> &T {
                self.value.as_ref().unwrap()
            }
        }
        impl<T: HashConsable> DerefMut for HashConsedMutRef<'_, T> {
            fn deref_mut(&mut self) -> &mut T {
                self.value.as_mut().unwrap()
            }
        }
        impl<T: HashConsable> Drop for HashConsedMutRef<'_, T> {
            fn drop(&mut self) {
                let value = self.value.take().unwrap();
                // Re-intern the new value if it changed.
                if value != *self.hc.inner() {
                    *self.hc = HashConsed::new(value);
                }
            }
        }
        let value = Some(self.inner().clone());
        HashConsedMutRef { hc: self, value }
    }
    /// Clones the inner value to get mutable access to it, and re-interns it afterwards (even if
    /// `f` panics).
    pub fn with_inner_mut<R>(&mut self, f: impl FnOnce(&mut T) -> R) -> R {
        f(&mut self.as_mut())
    }
}

impl<T> Deref for HashConsed<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.inner()
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for HashConsed<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("HashConsed").field(self.inner()).finish()
    }
}

impl<'s, T, V: Visit<'s, T>> Drive<'s, V> for HashConsed<T> {
    fn drive_inner(&'s self, v: &mut V) -> ControlFlow<V::Break> {
        v.visit(self.inner())
    }
}
impl<'s, T, V: VisitTwo<'s, T>> DriveTwo<'s, V> for HashConsed<T> {
    fn drive_two_inner(&'s self, other: &'s Self, v: &mut V) -> ControlFlow<V::Break> {
        v.visit(self.inner(), other.inner())
    }
}
/// Note: this explores the inner value mutably by cloning and re-hashing afterwards.
impl<'s, T, V> DriveMut<'s, V> for HashConsed<T>
where
    T: HashConsable,
    V: for<'a> VisitMut<'a, T>,
{
    fn drive_inner_mut(&'s mut self, v: &mut V) -> ControlFlow<V::Break> {
        self.with_inner_mut(|inner| v.visit(inner))
    }
}

/// `HashCons` values are deduplicated in the serialized output: see [`crate::utils::dedup`].
mod serialize {
    use serde::{Deserialize, Serialize};
    use serde_state::{DeserializeState, SerializeState};

    use super::{HashConsable, HashConsed};
    use crate::utils::dedup::*;

    impl<T> Serialize for HashConsed<T>
    where
        T: Serialize + HashConsable,
    {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            SerDedup::Untagged(self.inner()).serialize(serializer)
        }
    }
    /// Options for the state are `()` to serialize values normally and `DedupSerializer`
    /// to deduplicate identical values in the serialized output.
    impl<T, State> SerializeState<State> for HashConsed<T>
    where
        T: SerializeState<State> + HashConsable,
        State: DedupSerializerState,
    {
        fn serialize_state<S>(&self, state: &State, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            serialize_dedup(self, || self.inner(), state, serializer)
        }
    }

    impl<'de, T> Deserialize<'de> for HashConsed<T>
    where
        T: Deserialize<'de> + HashConsable,
    {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            use serde::de::Error;
            let repr: SerDedup<T> = SerDedup::deserialize(deserializer)?;
            match repr {
                SerDedup::Value { .. } | SerDedup::Deduplicated { .. } => {
                    Err(D::Error::custom(stateless_deserialize_error::<T>()))
                }
                SerDedup::Untagged(val) => Ok(HashConsed::new(val)),
            }
        }
    }
    impl<'de, T, State> DeserializeState<'de, State> for HashConsed<T>
    where
        T: DeserializeState<'de, State> + HashConsable,
        State: DedupSerializerState,
    {
        fn deserialize_state<D>(state: &State, deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            deserialize_dedup(state, deserializer, HashConsed::new)
        }
    }
}

#[test]
fn test_hash_cons() {
    let x = HashConsed::new(42u32);
    let y = HashConsed::new(42u32);
    assert_eq!(x, y);
    // Test a serialization round-trip.
    let z = serde_json::from_value(serde_json::to_value(x.clone()).unwrap()).unwrap();
    assert_eq!(x, z);
}

#[test]
fn test_hash_cons_concurrent() {
    use itertools::Itertools;
    let handles = (0..10)
        .map(|_| std::thread::spawn(|| std::hint::black_box(HashConsed::new(42u32))))
        .collect_vec();
    let values = handles.into_iter().map(|h| h.join().unwrap()).collect_vec();
    assert!(values.iter().all_equal())
}

#[test]
fn test_hash_cons_dedup() {
    use crate::utils::dedup::DedupSerializer;
    use serde_state::{DeserializeState, SerializeState};
    type Ty = HashConsed<TyKind>;
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    #[derive(SerializeState, DeserializeState)]
    #[serde_state(state = DedupSerializer)]
    enum TyKind {
        Bool,
        Pair(Ty, Ty),
    }

    // Build a value with some redundancy.
    let bool1 = HashConsed::new(TyKind::Bool);
    let bool2 = HashConsed::new(TyKind::Bool);
    let pair = HashConsed::new(TyKind::Pair(bool1.clone(), bool2));
    let triple = HashConsed::new(TyKind::Pair(bool1, pair));

    let state = DedupSerializer::default();
    let json_val = triple
        .serialize_state(&state, serde_json::value::Serializer)
        .unwrap();
    let state = DedupSerializer::default();
    let round_tripped = Ty::deserialize_state(&state, json_val).unwrap();

    assert_eq!(triple, round_tripped);
}
