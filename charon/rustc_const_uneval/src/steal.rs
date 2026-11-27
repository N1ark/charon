//! Reading MIR that rustc may steal.
//!
//! Rustc steals the MIR of a local item once a later pass needs it, e.g. to evaluate a constant,
//! and panics if another thread is reading that MIR meanwhile. So while we read MIR, the providers
//! of the passes that steal it keep a copy of what they steal (see `copy_body`), and we read the
//! copy.
use rustc_data_structures::steal::Steal;
use rustc_hash::FxHashMap;
use rustc_index::IndexVec;
use rustc_middle::mir::{Body, Promoted};
use std::sync::RwLock;

/// The levels of MIR bodies that rustc steals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirLevel {
    Built,
    Promoted,
    Elaborated,
}

/// The copies of the MIR rustc stole while we read it, by the address of their `Steal`. The
/// `'static` stands for the `'tcx` of the only compilation session.
struct Stolen {
    /// The level of the bodies we read, if they may be stolen.
    level: Option<MirLevel>,
    bodies: FxHashMap<usize, Body<'static>>,
    promoteds: FxHashMap<usize, IndexVec<Promoted, Body<'static>>>,
}

/// Set while we read MIR. We hold this lock while reading a `Steal`, and the providers that steal
/// take it to copy the value first, so that they don't steal it while we read it. We never hold it
/// while running queries.
static STOLEN: RwLock<Option<Stolen>> = RwLock::new(None);

/// Copy the bodies at `level` and the promoted constants that rustc steals until `stop_reading`.
pub fn start_reading(level: Option<MirLevel>) {
    *STOLEN.write().unwrap() = Some(Stolen {
        level,
        bodies: Default::default(),
        promoteds: Default::default(),
    });
}

/// Stop copying the MIR rustc steals, and free the copies.
pub fn stop_reading() {
    *STOLEN.write().unwrap() = None;
}

/// The body of this `Steal`, unless it was stolen without us copying it.
pub fn read_body<'tcx>(steal: &Steal<Body<'tcx>>) -> Option<Body<'tcx>> {
    let stolen = STOLEN.read().unwrap();
    let copy = stolen
        .as_ref()
        .and_then(|stolen| stolen.bodies.get(&addr(steal)));
    match copy {
        // SAFETY: see `Stolen`.
        Some(body) => {
            Some(unsafe { std::mem::transmute::<Body<'static>, Body<'tcx>>(body.clone()) })
        }
        None => (!steal.is_stolen()).then(|| steal.borrow().clone()),
    }
}

/// The promoted constant `promoted` of this `Steal`, unless it was stolen without us copying it.
pub fn read_promoted<'tcx>(
    steal: &Steal<IndexVec<Promoted, Body<'tcx>>>,
    promoted: Promoted,
) -> Option<Body<'tcx>> {
    let stolen = STOLEN.read().unwrap();
    let copy = stolen
        .as_ref()
        .and_then(|stolen| stolen.promoteds.get(&addr(steal)));
    match copy {
        // SAFETY: see `Stolen`.
        Some(promoteds) => Some(unsafe {
            std::mem::transmute::<Body<'static>, Body<'tcx>>(promoteds[promoted].clone())
        }),
        None => (!steal.is_stolen()).then(|| steal.borrow()[promoted].clone()),
    }
}

fn addr<T>(steal: &Steal<T>) -> usize {
    steal as *const Steal<T> as usize
}

/// Called by the providers that steal a body at `level`, before they steal it.
pub fn copy_body<'tcx>(level: MirLevel, steal: &Steal<Body<'tcx>>) {
    if let Some(stolen) = &mut *STOLEN.write().unwrap()
        && stolen.level == Some(level)
        && !steal.is_stolen()
    {
        // SAFETY: see `Stolen`.
        let body =
            unsafe { std::mem::transmute::<Body<'tcx>, Body<'static>>(steal.borrow().clone()) };
        stolen.bodies.insert(addr(steal), body);
    }
}

/// Called by the providers that steal promoted constants, before they steal them.
pub fn copy_promoteds<'tcx>(steal: &Steal<IndexVec<Promoted, Body<'tcx>>>) {
    if let Some(stolen) = &mut *STOLEN.write().unwrap()
        && !steal.is_stolen()
    {
        // SAFETY: see `Stolen`.
        let promoteds = unsafe {
            std::mem::transmute::<IndexVec<Promoted, Body<'tcx>>, IndexVec<Promoted, Body<'static>>>(
                steal.borrow().clone(),
            )
        };
        stolen.promoteds.insert(addr(steal), promoteds);
    }
}
