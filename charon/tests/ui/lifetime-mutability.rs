struct A<'a, 'b> {
    x: &'a mut u32,
    y: &'b u32,
    z: Box<&'b mut u32>,
}

struct B<'a, 'b>(A<'a, 'b>);

// Only the first lifetime of `E` is used mutably; `F` passes it its second lifetime.
struct E<'a, 'b> {
    x: &'a mut u32,
    y: &'b u32,
}

struct F<'a, 'b>(E<'b, 'a>);
