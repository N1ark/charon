//@ output=run-with-minirust
//@ known-ub
// Constant pointers with projections and offsets into globals.
unsafe extern "Rust" {
    safe fn minirust_print(value: u32);
}

static ARR: [u32; 3] = [10, 20, 0x0102_0304];
static ANON: &[u32; 3] = &[1, 2, 3];
static ANON_TAIL: &u32 = &ANON[2];
static ARR2: [u32; 3] = [10, 20, 30];
static ARR2D: [[u8; 2]; 2] = [[1, 2], [3, 4]];

fn main() {
    // One past the end: a typed in-bounds offset followed by a cast.
    let end = const { unsafe { (&raw const ARR).cast::<u32>().add(3) } };
    minirust_print(unsafe { *end.sub(1) });
    // Out of bounds: a wrapping offset.
    let oob = const { (&raw const ARR).cast::<u32>().wrapping_add(5) };
    minirust_print(unsafe { *oob.wrapping_sub(4) });
    let before = const { (&raw const ARR).cast::<u32>().wrapping_sub(1) };
    minirust_print(unsafe { *before.wrapping_add(1) });
    // A byte offset followed by a cast.
    let mis = const { unsafe { (&raw const ARR).cast::<u8>().add(4).cast::<u32>() } };
    minirust_print(unsafe { *mis });
    // A field projection.
    let field: &u32 = const { &ARR[1] };
    minirust_print(*field);
    // A cast followed by an unsizing cast.
    let words: &[u16] =
        const { unsafe { core::slice::from_raw_parts((&raw const ARR).cast::<u16>(), 2) } };
    minirust_print(words[0] as u32);
    let b = const { unsafe { (&raw const ARR).cast::<u8>().add(9) } };
    minirust_print(unsafe { *b } as u32);
    let h = const { unsafe { (&raw const ARR).cast::<u8>().add(9).cast::<u16>() } };
    minirust_print(unsafe { h.read_unaligned() } as u32);
    // A relocation with an offset into an anonymous allocation.
    minirust_print(*ANON_TAIL);
    // A pointee that extends past the end of the allocation.
    let tail = const { unsafe { (&raw const ARR2).cast::<u32>().add(2).cast::<[u32; 2]>() } };
    minirust_print(unsafe { *tail.cast::<u32>() });
    // A slice straddling two rows.
    let mid: &[u8] = const {
        unsafe { core::slice::from_raw_parts((&raw const ARR2D).cast::<u8>().add(1), 2) }
    };
    minirust_print(mid[0] as u32 * 10 + mid[1] as u32);
}
