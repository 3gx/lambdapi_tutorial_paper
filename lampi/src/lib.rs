#![feature(box_patterns, box_syntax)]

#[macro_export]
macro_rules! clone {
    ($i:ident) => {
        let $i = $i.clone();
    };
    ($i:ident, $($tt:tt)*) => {
        clone!($i);
        clone!($($tt)*);
    };
    /*
    ($this:ident . $i:ident) => {
        let $i = $this.$i.clone();
    };
    ($this:ident . $i:ident, $($tt:tt)*) => {
        clone!($this . $i);
        clone!($($tt)*);
    };
    */
}
#[macro_export]
macro_rules! rc_closure {
    ({}, $closure:expr) => {
        Rc::new($closure)
    };
    ({$($tt:tt)*}, $closure:expr) => {
        {
        clone!($($tt)*);
        Rc::new($closure)
        }
    };
}

pub mod dtlc;

pub mod stlc;
