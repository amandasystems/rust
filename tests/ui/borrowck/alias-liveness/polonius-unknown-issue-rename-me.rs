#![forbid(unsafe_code)]

// This one says that a outlives 
type P<'a, 'b> = for<'x> fn(&'a mut &'b Box<i32>, &'x ()) -> &'x Box<i32>;

fn f<'a, 'b, 'c>(x: &'a mut &'b Box<i32>, _: &'c ()) -> &'b Box<i32> {
    *x
}

fn main() {
    let p: &'static mut Box<i32> = Box::leak(Box::new(Box::new(1))); // p is 'static
    let mid: &mut &Box<i32> = Box::leak(Box::new(&*p)); //  reborrow p into mid
    let r: &Box<i32> = (f as P<'_, '_>)(mid, &()); // ??? probably introduce contravariance
    let b: &i32 = r.as_ref();
    if false {
        let _: &mut &'static Box<i32> = mid; // this branch is load bearing for the bug!
    } else { // b is an alias of p
        *p = Box::new(17); // ERROR `*p` is assigned to here but it was already borrowed
        println!("{b}");
    };
}
