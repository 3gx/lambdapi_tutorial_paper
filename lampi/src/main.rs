#![feature(box_patterns, box_syntax)]
fn main() {
    println!("answer= {}", lampi::stlc::test());
    println!("Hello, world!");

    use std::cell::RefCell;
    use std::rc::Rc;
    struct T(Rc<dyn Fn(i32) -> i32>);
    impl T {
        fn new(f: Rc<dyn Fn(i32) -> i32>) -> T {
            T(f)
        }
        fn clone(&self) -> T {
            T::new(Rc::clone(&self.0))
        }
    }

    let a = T::new(Rc::new(|x| x + 3));
    println!("count= {}", Rc::strong_count(&a.0));
    let b = a.clone();
    println!("count= {}", Rc::strong_count(&b.0));

    #[derive(Clone, Debug)]
    struct U(Rc<i32>);

    let a = U(Rc::new(5));
    println!("count= {}", Rc::strong_count(&a.0));
    let b = a.clone();
    println!("count= {}", Rc::strong_count(&a.0));
    println!("count= {}", Rc::strong_count(&b.0));
    let c = b.clone();
    println!("count= {}", Rc::strong_count(&a.0));
    println!("count= {}", Rc::strong_count(&b.0));
    println!("count= {}", Rc::strong_count(&c.0));
    println!("count= {:?} {:?} {:?}", a, b, c);

    #[derive(Clone, Debug)]
    struct V(Rc<RefCell<i32>>);

    let a = V(Rc::new(RefCell::new(5)));
    println!("count= {}", Rc::strong_count(&a.0));
    let b = a.clone();
    println!("count= {}", Rc::strong_count(&a.0));
    println!("count= {}", Rc::strong_count(&b.0));
    let c = b.clone();
    println!("count= {}", Rc::strong_count(&a.0));
    println!("count= {}", Rc::strong_count(&b.0));
    println!("count= {}", Rc::strong_count(&c.0));
    println!("count= {:?} {:?} {:?}", a, b, c);

    *b.0.borrow_mut() = 42;
    println!("count= {}", Rc::strong_count(&a.0));
    println!("count= {}", Rc::strong_count(&b.0));
    println!("count= {}", Rc::strong_count(&c.0));
    println!("count= {:?} {:?} {:?}", a, b, c);

    {
        use lampi::stlc::{TermC::*, TermI::*, Type::*, Name::*, Boxed};
        let id1 = Lam(Inf(Bound(0).b()).b());
        let const1 = Lam(Lam(Inf(Bound(1).b()).b()).b());
        let tfree = |a : &str| TFree(Global(a.to_string()).b()).b();
        let free = |x : &str| Inf(Free(Global(x.to_string()).b()).b()).b();
        let term1 = App(Ann(id1.b(), Fun(tfree("a"), tfree("a")).b()).b(), free("y")).b();
        let term2 = App(App(Ann(const1.b(), Fun(Fun(tfree("b"), tfree("b")).b(),
                   Fun(tfree("a"),
                        Fun(tfree("b"),tfree("b")).b()).b()).b()).b(), id1.b()).b(), free("y")).b();
        println!("term1= {:?}",term1);
        println!("term2= {:?}",term2);
    }
}
