//@ charon-args=--monomorphize
//@ scramble-order=3
// The vtables of these impls are translated, so the impls refer to them whatever the order in
// which we translate items. The sources of the impls that the vtables register differ from those
// of the translated impls in how they represent the regions of the closure signature.
pub struct W<'a>(&'a mut u32);
pub struct B<'a>(&'a u8);

fn call(f: &mut dyn FnMut(&mut W<'_>, B<'_>) -> bool) -> bool {
    let mut x = 0;
    f(&mut W(&mut x), B(&1))
}

fn call_once(f: Box<dyn FnOnce(&mut W<'_>, B<'_>) -> bool>) -> bool {
    let mut x = 0;
    f(&mut W(&mut x), B(&1))
}

pub fn main() {
    let mut c = move |w: &mut W<'_>, b: B<'_>| {
        *w.0 += *b.0 as u32;
        true
    };
    call(&mut c);
    call_once(Box::new(c));
}
