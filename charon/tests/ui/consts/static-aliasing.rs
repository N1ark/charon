//@charon-args=--consts=values
// Pointers to and into other statics must keep pointing to the same place.
struct Sync<T>(T);
unsafe impl<T> std::marker::Sync for Sync<T> {}

static ARR: [u32; 3] = [1, 2, 3];
static FIRST: &u32 = &ARR[0];
static SECOND: &u32 = &ARR[1];
static WHOLE: &[u32; 3] = &ARR;
static SLICE: &[u32] = &ARR;
static PREFIX: &[u32] = ARR.split_at(2).0;
static SUFFIX: &[u32] = ARR.split_at(1).1;
static END: Sync<*const u32> = Sync(unsafe { (&raw const ARR).cast::<u32>().add(3) });
static BYTE: Sync<*const u8> = Sync(unsafe { (&raw const ARR).cast::<u8>().add(5) });

struct S {
    a: u32,
    b: (u8, u64),
}
static S0: S = S { a: 1, b: (2, 3) };
static B: &u64 = &S0.b.1;

enum E {
    A(u8),
    B(u16, u32),
}
static E0: E = E::B(4, 5);
static E0_FIELD: &u32 = match &E0 {
    E::B(_, x) => x,
    E::A(..) => &0,
};

static NESTED: [S; 2] = [S { a: 1, b: (2, 3) }, S { a: 4, b: (5, 6) }];
static NESTED_FIELD: &u8 = &NESTED[1].b.0;

static mut MUT: [u32; 2] = [0, 0];
static MUT_PTR: Sync<*mut u32> = Sync(unsafe { (&raw mut MUT).cast::<u32>().add(1) });

struct WithArray {
    a: u8,
    arr: [u16; 4],
}
static WITH_ARRAY: WithArray = WithArray {
    a: 0,
    arr: [1, 2, 3, 4],
};
static MIDDLE: &[u16] = WITH_ARRAY.arr.split_at(1).1.split_at(2).0;

// Pointers into anonymous allocations.
static ANON: &(u32, u32) = &(1, 2);
static ANON_SECOND: &u32 = &ANON.1;
static ANON_SUFFIX: &[u32] = [1, 2, 3].as_slice().split_at(1).1;

fn main() {
    let _ = (FIRST, SECOND, WHOLE, SLICE, PREFIX, SUFFIX, &END, &BYTE);
    let _ = (B, E0_FIELD, NESTED_FIELD, &MUT_PTR, MIDDLE);
    let _ = (ANON_SECOND, ANON_SUFFIX);
}
