#![feature(box_patterns, box_syntax)]

#[macro_export]
macro_rules! clone_vars {
    ($i:ident) => {
        let $i = $i.clone();
    };
    ($i:ident, $($tt:tt)*) => {
        clone_vars!($i);
        clone_vars!($($tt)*);
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
        clone_vars!($($tt)*);
        Rc::new($closure)
        }
    };
}

pub mod dtlc;

pub mod stlc;
