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
        println!("");
        println!("-=- STLC -=-");
        use lampi::stlc::*;
        use {Info::*, Kind::*, Name::*, TermC::*, TermI::*, Type::*};
        let id1 = || box Lam(box Inf(box Bound(0)));
        let const1 = || box Lam(box Lam(box Inf(box Bound(1))));
        let tfree = |a: &str| box TFree(box Global(a.to_string()));
        let free = |x: &str| box Inf(box Free(box Global(x.to_string())));
        let term1 = box App(box Ann(id1(), box Fun(tfree("a"), tfree("a"))), free("y"));
        let term2 = App(
            box App(
                box Ann(
                    const1(),
                    box Fun(
                        box Fun(tfree("b"), tfree("b")),
                        box Fun(tfree("a"), box Fun(tfree("b"), tfree("b"))),
                    ),
                ),
                id1(),
            ),
            free("y"),
        );
        println!("term1= {:?}", term1);
        println!("term2= {:?}", term2);

        let global = |x: &str| Global(x.to_string());
        let hastype = |t: Type| HasType(box t);
        let haskind = |k: Kind| HasKind(box k);
        let env1 = Ctx::from(vec![
            (global("y"), hastype(*tfree("a"))),
            (global("a"), haskind(Star)),
        ]);
        let mut env2 = env1.clone();
        env2.push_front((global("b"), haskind(Star)));

        let t0 = evalI(&term1, &Env::new());
        println!("t0= {:?}", t0);
        let t1 = quote0(&evalI(&term1, &Env::new()));
        println!("t1= {:?}", t1);
        let t2 = quote0(&evalI(&term2, &Env::new()));
        println!("t2= {:?}", t2);
        let t3 = typeI0(&env1, &term1);
        println!("t3= {:?}", t3);
        let t4 = typeI0(&env2, &term2);
        println!("t4= {:?}", t4);
        let t5 = typeI0(&env1, &term2);
        println!("t5= {:?}", t5);
    }

    {
        println!("");
        println!("-=- DTLC -=-");
    }
}
