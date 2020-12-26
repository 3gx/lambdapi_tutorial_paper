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
macro_rules! rclam {
    ({}, || $body:expr) => {
        Rc::new(move || $body)
    };
    ({}, |$($vars:tt),*| $body:expr) => {
        Rc::new(move |$($vars),*| $body)
    };
    ({$($captures:tt),*}, || $body:expr) => {
        {
        clone_vars!($($captures),*);
        Rc::new(move || $body)
        }
    };
    ({$($captures:tt),*}, |$($vars:tt),*| $body:expr) => {
        {
        clone_vars!($($captures),*);
        Rc::new(move |$($vars),*| $body)
        }
    };
}

#[macro_export]
macro_rules! rc_closure {
    ({}, |$var:tt| $body:expr) => {
        Rc::new(move |$var| $body)
    };
    ({}, |$var:tt, $($vars:tt),*| $body:expr) => {
        Rc::new(move |$var, $($vars)*| $body)
    };
    ({$($tt:tt)*}, |$var:tt| $body:expr) => {
        {
        clone_vars!($($tt)*);
        Rc::new(move |$var| $body)
        }
    };
    ({$($tt:tt)*}, |$var:tt, $($vars:tt)*| $body:expr) => {
        {
        clone_vars!($($tt)*);
        Rc::new(move |$var, $($vars)*| $body)
        }
    };
    ({}, |$var:tt| $body:expr) => {
        Rc::new(move |$var| $body)
    };
    ({}, |$var:tt, $($vars:tt)*| $body:expr) => {
        Rc::new(move |$var, $($vars)*| $body)
    };
    ({$($tt:tt)*}, |$var:tt| $body:expr) => {
        {
        clone_vars!($($tt)*);
        Rc::new(move |$var| $body)
        }
    };
    ({$($tt:tt)*}, |$var:tt, $($vars:tt)*| $body:expr) => {
        {
        clone_vars!($($tt)*);
        Rc::new(move |$var, $($vars)*| $body)
        }
    };
}

pub mod dtlc;

pub mod stlc;
