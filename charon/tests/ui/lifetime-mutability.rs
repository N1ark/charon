struct A<'a, 'b> {
    x: &'a mut u32,
    y: &'b u32,
    z: Box<&'b mut u32>,
}

struct B<'a, 'b>(A<'a, 'b>);

// `C` and `D` mention each other: `D`'s lifetime is used mutably through `C`, whichever we analyze
// first.
struct C<'a> {
    d: Option<Box<D<'a>>>,
    x: &'a mut u32,
}

struct D<'a> {
    c: Option<Box<C<'a>>>,
}

// Only the first lifetime of `E` is used mutably; `F` passes it its second lifetime.
struct E<'a, 'b> {
    x: &'a mut u32,
    y: &'b u32,
}

struct F<'a, 'b>(E<'b, 'a>);
