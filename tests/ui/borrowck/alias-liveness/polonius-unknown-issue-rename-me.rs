
type P<'a, 'b> = for<'x> fn(&'a mut &'b u8, &'x ()) -> &'x u8;

fn f<'a, 'b, 'c>(x: &'a mut &'b u8, _: &'c ()) -> &'b u8 {
    *x
}

fn main() {
    let p: &'static mut u8 = Box::leak(Box::new(0));
    let mid: &mut &u8 = Box::leak(Box::new(&*p));
    let r: &u8 = (f as P<'_, '_>)(mid, &());
    //
    if false {
        let _: &mut &'static u8 = mid; 
    } else {
        *p = 1;
        assert_eq!(*r, 1);  // r and p alias
    };
}
