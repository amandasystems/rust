type P<'a, 'b> = for<'x> fn(&'a mut &'b i32, &'x ()) -> &'x i32;

fn f<'a, 'b, 'c>(x: &'a mut &'b i32, _: &'c ()) -> &'b i32 {
    *x
}

fn main() {
    let p = Box::leak(Box::new(1));
    let mid: &mut &i32 = Box::leak(Box::new(p));
    let b = *(f as P<'_, '_>)(mid, &());
    if false {
        let _: &mut &'static i32 = mid;
    } else {
        drop(p);
        drop(b); // `p` droppped again here via alias in `b`!
    }
}
