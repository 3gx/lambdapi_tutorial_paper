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
        let _plusl = |x: TermC| {
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

        /*
        ## > let plus = natElim (\_ -> Nat -> Nat)
        ##                      (\n -> n)
        ##                      (\k rec n -> Succ (rec n))
        ## plus :: Pi (x :: Nat) (y :: Nat) . Nat

        plusl: TLam[[TermC], TermI] = lambda x: NatElim(
            Lam(pi(Inf(Nat()), Inf(Nat()))),
            Lam(Inf(Bound(0))),
            Lam(Lam(Lam(Inf(Succ(Inf(App(Bound(1), Inf(Bound(0))))))))),
            x,
        )

        natElimL = Lam(
            Lam(
                Lam(
                    Lam(
                        Inf(NatElim(Inf(Bound(3)), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0))))
                    )
                )
            )
        )
        natElimTy = VPi(
            VPi(VNat(), lambda _: VStar()),
            lambda m: VPi(
                vapp(m, VZero()),
                lambda _: VPi(
                    VPi(VNat(), lambda k: VPi(vapp(m, k), lambda _: vapp(m, VSucc(k)))),
                    lambda _: VPi(VNat(), lambda n: vapp(m, n)),
                ),
            ),
        )

        natElim = Ann(natElimL, quote0(natElimTy))
        print("natElim=", natElim)
        print("type(natElim)=", typeI0({}, natElim))
        Plus = App(
            App(App(natElim, Lam(pi(Inf(Nat()), Inf(Nat())))), Lam(Inf(Bound(0)))),
            Lam(Lam(Lam(Inf(Succ(Inf(App(Bound(1), Inf(Bound(0))))))))),
        )
        VnatElim = evalI(natElim, [])
        vplus = vapply(VnatElim, [\
                VLam(lambda _: VPi(VNat(), lambda _ : VNat())),
                VLam(lambda n : n),
                VLam(lambda p: VLam(lambda rec: VLam(lambda n : VSucc(vapp(rec, n)))))])
        print("vplus=", vplus)
        #Plus2 : TermI
        #plus2env : Context
        #plus2env = {Global("VnatElim"): natElimTy}
        #Plus2, _ = (quote0(vplus) >> Inf).e >> App
        #print("plus2env=", plus2env)
        #print("Plus2=",Plus2)
        #print("type(Plus2)=", typeI0(plus2env, Plus2))
                 */
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
