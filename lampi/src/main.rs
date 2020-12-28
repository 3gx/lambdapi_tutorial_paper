#![feature(box_patterns, box_syntax)]

macro_rules! clone_all {
    ($i:ident) => {
        let $i = $i.clone();
    };
    ($i:ident, $($tt:tt)*) => {
        clone_all!($i);
        clone_all!($($tt)*);
    };
    ($this:ident . $i:ident) => {
        let $i = $this.$i.clone();
    };
    ($this:ident . $i:ident, $($tt:tt)*) => {
        clone_all!($this . $i);
        clone_all!($($tt)*);
    };
}

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
        let env2 = Ctx::from([&[(global("b"), haskind(Star))], &env1[..]].concat());

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
        use lampi::dtlc::*;
        use lampi::rclam;
        use {Name::*, Neutral::*, TermC::*, TermI::*, Value::*};

        let v0 = VLam(rclam![{}, |x| VLam(rclam![{ x }, |_| x.dup()])]);
        println!("v0={:?}", v0);
        let e0 = quote0(&v0);
        println!("e0={:?}", e0);

        let c = rclam!({}, |x, y| x + y);
        println!("{}", c(2, 3));

        let id_ = || Lam(box Inf(box Bound(0)));
        let const_ = || Lam(box Lam(box Inf(box Bound(1))));
        let free = |x: &str| Inf(box Free(box Global(x.to_string())));
        let pi = |x, y| Inf(box Pi(x, y));
        let term1 = App(
            box Ann(box id_(), box pi(box free("a"), box free("a"))),
            box free("y"),
        );
        let term2 = App(
            box App(
                box Ann(
                    box const_(),
                    box pi(
                        box pi(box free("b"), box free("b")),
                        box pi(box free("a"), box pi(box free("b"), box free("b"))),
                    ),
                ),
                box id_(),
            ),
            box free("y"),
        );
        let env1 = Context::from(vec![
            (
                Global("y".to_string()),
                VNeutral(box NFree(box Global("a".to_string()))),
            ),
            (Global("a".to_string()), VStar),
        ]);
        let env2 = Context::from([&[(Global("b".to_string()), VStar)], &env1[..]].concat());
        println!("eval(term1)= {:?}", evalI(&term1, &Env::new()));
        println!("qeval(term1)= {:?}", quote0(&evalI(&term1, &Env::new())));
        println!("qqeval(term2)= {:?}", quote0(&evalI(&term2, &Env::new())));
        println!("type(term1)= {:?}", typeI0(&env1, &term1));
        println!("type(term2)= {:?}", typeI0(&env2, &term2));

        // example for the following concrete syntax
        // > let id = (\a x -> x) :: Pi (a :: *).a -> a
        // id :: Pi (x::*) (y::x).x
        let e35 = Ann(
            box Lam(box Lam(box Inf(box Bound(0)))),
            box pi(
                box Inf(box Star),
                box pi(box Inf(box Bound(0)), box Inf(box Bound(1))),
            ),
        );
        println!("e35= {:?}", e35);

        macro_rules! bx {
            ($e:expr) => {
                $e.b()
            };
        }

        let env35 = Context::from(vec![
            (Global("Bool".to_string()), VStar),
            (
                Global("False".to_string()),
                VNeutral(bx![NFree(bx![Global("Bool".to_string())])]),
            ),
        ]);
        println!("type(e35)= {:?}", typeI0(&env35, &e35));

        let apply35a = App(e35.b(), box free("Bool"));
        println!("apply35a= {:?}", apply35a);
        println!("type(apply35a)= {:?}", typeI0(&env35, &apply35a));

        let apply35b = App(apply35a.b(), box free("False"));
        println!("apply35b= {:?}", apply35b);
        println!("type(apply35b)= {:?}", typeI0(&env35, &apply35b));

        // > let plus = natElim (\_ -> Nat -> Nat)
        //                      (\n -> n)
        //                      (\k rec n -> Succ (rec n))
        // plus :: Pi (x :: Nat) (y :: Nat) . Nat
        let plusl = |x: &TermC| {
            NatElim(
                box Lam(box pi(box Inf(box Nat), box Inf(box Nat))),
                box Lam(box Inf(box Bound(0))),
                box Lam(box Lam(box Lam(box Inf(box Succ(box Inf(box App(
                    box Bound(1),
                    box Inf(box Bound(0)),
                ))))))),
                x.b(),
            )
        };

        let nat_elim_l = Lam(box Lam(box Lam(box Lam(box Inf(box NatElim(
            box Inf(box Bound(3)),
            box Inf(box Bound(2)),
            box Inf(box Bound(1)),
            box Inf(box Bound(0)),
        ))))));

        let nat_elim_ty = VPi(
            box VPi(box VNat, rclam![{}, |_| VStar]),
            rclam![{}, |m| VPi(
                box vapp(&m, &VZero),
                rclam![{ m }, |_| VPi(
                    box VPi(
                        box VNat,
                        rclam![{ m }, |k| VPi(
                            box vapp(&m, &k),
                            rclam![{m,k}, |_| vapp(&m, &VSucc(k.b()))]
                        )]
                    ),
                    rclam![{ m }, |_| VPi(box VNat, rclam![{ m }, |n| vapp(&m, &n)])],
                )],
            )],
        );
        let nat_elim = Ann(nat_elim_l.b(), quote0(&nat_elim_ty).b());
        println!("nat_elim= {:?}", nat_elim);
        println!("type(nat_elim)= {:?}", typeI0(&Context::new(), &nat_elim));

        let plus = App(
            box App(
                box App(
                    nat_elim.b(),
                    box Lam(box pi(box Inf(box Nat), box Inf(box Nat))),
                ),
                box Lam(box Inf(box Bound(0))),
            ),
            box Lam(box Lam(box Lam(box Inf(box Succ(box Inf(box App(
                box Bound(1),
                box Inf(box Bound(0)),
            ))))))),
        );
        let vnat_elim = evalI(&nat_elim, &Env::new());
        let vplus = vapply(
            &vnat_elim,
            &vec![
                VLam(rclam![{}, |_| VPi(box VNat, rclam![{}, |_| VNat])]),
                VLam(rclam![{}, move |n| n.dup()]),
                VLam(rclam![{}, |_| VLam(rclam![{}, |rec| VLam(rclam![
                    { rec },
                    |n| VSucc(box vapp(&rec, &n))
                ])])]),
            ],
        );
        println!("vplus={:?}", vplus);

        let plus2env = Context::from(vec![(Global("VnatElim".to_string()), nat_elim_ty.dup())]);
        println!("plus2env= {:?}", plus2env);
        /*
        if let Lam(box Inf(box App(plus2, _))) = quote0(&vplus) {
            println!("plus2= {:?}",plus2);
            println!("type(plus2)= {:?}", typeI0(&plus2env, &plus2));
        } else {
           panic!("unhandled {:?}", vplus);
        }
        */

        let plus1 = Ann(
            box Lam(box Inf(box NatElim(
                box Lam(box pi(box Inf(box Nat), box Inf(box Nat))),
                box Lam(box Inf(box Bound(0))),
                box Lam(box Lam(box Lam(box Inf(box Succ(box Inf(box App(
                    box Bound(1),
                    box Inf(box Bound(0)),
                ))))))),
                box Inf(box Bound(0)),
            ))),
            box pi(box Inf(box Nat), box pi(box Inf(box Nat), box Inf(box Nat))),
        );
        println!("type(plus1)= {:?}", typeI0(&Context::new(), &plus1));
        println!("type(Plus)= {:?}", typeI0(&Context::new(), &plus));

        fn int2nat(n: Int) -> TermC {
            if n == 0 {
                Inf(box Zero)
            } else {
                Inf(box Succ(box int2nat(n - 1)))
            }
        }

        fn nval2int(v: &Value) -> Int {
            match v {
                VZero => 0,
                VSucc(k) => 1 + nval2int(k),
                _ => panic!("unhandled {:?}", v),
            }
        }
        // > plus 40 2
        //# 42 :: Nat
        let n40 = int2nat(40);
        println!("n40= {:?}", n40);
        let n2 = int2nat(2);
        println!("n2= {:?}", n2);
        if let Inf(ti) = &n40 {
            println!("type(n40)= {:?}", typeI0(&Context::new(), &ti));
        } else {
            panic!("unsupported {:?}", n40);
        }
        println!(
            "type(plusl(n40))= {:?}",
            typeI0(&Context::new(), &plusl(&n40))
        );
        let n42term = App(box plusl(&n40), n2.b());
        println!("type(n42term)= {:?}", typeI0(&Context::new(), &n42term));
        let n42v = evalI(&n42term, &Env::new());
        println!("n42v= {:?}", n42v);
        let n42 = nval2int(&n42v);
        println!("n42= {:?}", n42);
        // > n42
        // 42
        let n1 = int2nat(1);
        let n2a = App(plusl(&n1).b(), n1.b());

        println!("n2a= {:?}", n2a);
        println!("type(n2a)= {:?}", typeI0(&Context::new(), &n2a));
        let n2e = evalI(&n2a, &Env::new());
        println!("n2e= {:?}", n2e);
        println!("n2e= {:?}", nval2int(&n2e));
        let n4 = App(plusl(&Inf(n2a.b())).b(), Inf(n2a.b()).b());
        println!("n4= {:?}", n4);
        println!("type(n4)= {:?}", typeI0(&Context::new(), &n4));
        println!("eval(n4)= {:?}", nval2int(&evalI(&n4, &Env::new())));
    }

    {
        //        use std::rc::Rc;
        fn closure_user(closure: Box<dyn Fn(usize) -> bool>) -> bool {
            closure(3)
        }

        let big_data = box vec![1, 2, 3, 4];
        closure_user({
            clone_all!(big_data);
            //            let big_data = big_data.clone();
            Box::new(move |x| {
                println!("big_data= {:?}  x={}", big_data, x);
                false
            })
        });
        println!("big_data= {:?}", big_data);
    }
}
