use std::rc::Rc;
//#[macro_use]

/*
macro_rules! closure {
    ([$($tt:tt)*], $closure:expr) => {
        {
        clone!($($tt)*);
        $closure
        }
    };
}
*/

/*
macro_rules! rc_closure1 {
    ({$($tt:tt)*}, |$var:ident| $body:expr) => {
        {
        clone_vars!($($tt)*);
        Rc::new(move |$var| $body)
        }
    };
    ({$($tt:tt)*}, |$var:ident, $($vars:ident)*| $body:expr) => {
        {
        clone_vars!($($tt)*);
        Rc::new(move |$var, $($vars)*| $body)
        }
    };
}
*/
/*
macro_rules! closure1 {
    ([$($tt:tt)*], $closure:expr) => {
        {
        clone!($($tt)*);
        $closure
        }
    };
}
*/

pub type Int = i32;

pub trait Dup: Sized + Clone {
    fn b(self: &Self) -> Box<Self> {
        box self.clone()
    }
    fn dup(self: &Self) -> Self {
        self.clone()
    }
}

struct Fix<'a, T, U> {
    f: &'a dyn Fn(&Fix<'a, T, U>, T) -> U,
}

impl<'a, T, U> Fix<'a, T, U> {
    fn call(&self, x: T) -> U {
        (self.f)(self, x)
    }
}
macro_rules! fix {
    ($e:expr) => {
        Fix { f: &$e }
    };
}

/*
struct FixOnce<'a, T, U> {
    f: &'a dyn FnOnce(&FixOnce<'a, T, U>, T) -> U,
}

impl<'a, T, U> FixOnce<'a, T, U> {
    fn call(&self, x: T) -> U {
        (self.f)(self, x)
    }
}

macro_rules! fix_once {
    ($e:expr) => {
        FixOnce { f: &$e }
    };
}
*/

// ---------------------------------------------------------------------------

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum TermI {
    Ann(Box<TermC>, Box<TermC>),
    Star,
    Pi(Box<TermC>, Box<TermC>),
    Bound(Int),
    Free(Box<Name>),
    App(Box<TermI>, Box<TermC>),
    Nat,
    NatElim(Box<TermC>, Box<TermC>, Box<TermC>, Box<TermC>),
    Zero,
    Succ(Box<TermC>),
    Vec(Box<TermC>, Box<TermC>),
    Nil(Box<TermC>),
    Cons(Box<TermC>, Box<TermC>, Box<TermC>, Box<TermC>),
    VecElim(
        Box<TermC>,
        Box<TermC>,
        Box<TermC>,
        Box<TermC>,
        Box<TermC>,
        Box<TermC>,
    ),
}
impl Dup for TermI {}

// ---------------------------------------------------------------------------

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum TermC {
    Inf(Box<TermI>),
    Lam(Box<TermC>),
}
impl Dup for TermC {}

// ---------------------------------------------------------------------------

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Name {
    Global(String),
    Local(Int),
    Quote(Int),
}
impl Dup for Name {}

// ---------------------------------------------------------------------------

type VFun = Rc<dyn Fn(&Value) -> Value>;
#[derive(Clone)]
pub enum Value {
    VLam(VFun),
    VStar,
    VPi(Box<Value>, VFun),
    VNeutral(Box<Neutral>),
    VNat,
    VZero,
    VSucc(Box<Value>),
    VNil(Box<Value>),
    VCons(Box<Value>, Box<Value>, Box<Value>, Box<Value>),
    VVec(Box<Value>, Box<Value>),
}
impl Dup for Value {}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::VLam(..) => write!(f, "{:?}", quote0(&self)),
            Value::VStar => write!(f, "VStar"),
            Value::VPi(..) => write!(f, "{:?}", quote0(&self)),
            Value::VNeutral(n) => write!(f, "VNeutral({:?})", n),
            Value::VNat => write!(f, "VNat"),
            Value::VZero => write!(f, "VZero"),
            Value::VSucc(v) => write!(f, "VSucc({:?})", v),
            Value::VNil(v) => write!(f, "VNil({:?})", v),
            Value::VCons(v1, v2, v3, v4) => write!(f, "VCons{:?}", (v1, v2, v3, v4)),
            Value::VVec(v1, v2) => write!(f, "VVec{:?}", (v1, v2)),
        }
    }
}

// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum Neutral {
    NFree(Box<Name>),
    NApp(Box<Neutral>, Box<Value>),
    NNatElim(Box<Value>, Box<Value>, Box<Value>, Box<Neutral>),
    NVecElim(
        Box<Value>,
        Box<Value>,
        Box<Value>,
        Box<Value>,
        Box<Value>,
        Box<Neutral>,
    ),
}
impl Dup for Neutral {}

// ---------------------------------------------------------------------------

type Type = Value;

fn vfree(n: Name) -> Value {
    Value::VNeutral(box Neutral::NFree(box n))
}

pub type Env = Vec<Value>;
pub type Context = Vec<(Name, Type)>;
fn lookup<'a, 'b>(c: &'a Context, n: &'b Name) -> Option<&'a Type> {
    if let Some((_, i)) = c.iter().find(|x| x.0 == *n) {
        Some(i)
    } else {
        None
    }
}

#[allow(non_snake_case)]
pub fn evalI(trm: &TermI, env: &Env) -> Value {
    use {Neutral::*, TermI::*, Value::*};
    match trm {
        Ann(e, _) => evalC(e, env),
        Star => VStar,
        Pi(t, tp) => VPi(
            box evalC(t, env),
            lam![{tp, env} move |x| evalC(
                &tp,
                &[&[x.dup()], &env[..]].concat()
            )],
        ),
        Free(x) => vfree(x.dup()),
        Bound(i) => env[*i as usize].dup(),
        App(e, ep) => vapp(&evalI(e, env), &evalC(ep, env)),
        Nat => VNat,
        Zero => VZero,
        Succ(k) => VSucc(box evalC(k, env)),
        NatElim(box m, mz, ms, box k) => {
            let mzVal = evalC(mz, env);
            let msVal = evalC(ms, env);
            fix!(|rec, &ref kVal| match kVal {
                VZero => mzVal.dup(),
                VSucc(box ref l) => vapp(&vapp(&msVal, l), &rec.call(l)),
                VNeutral(box k) => VNeutral(box NNatElim(
                    box evalC(m, env),
                    box mzVal.dup(),
                    box msVal.dup(),
                    box k.dup(),
                )),
                _ => unreachable!(format!("unknown natElim match {:?}", kVal)),
            })
            .call(&evalC(k, env))
        }
        Vec(a, n) => VVec(box evalC(a, env), box evalC(n, env)),
        VecElim(a, m, mn, mc, n, xs) => {
            let mnVal = evalC(mn, env);
            let mcVal = evalC(mc, env);
            let frec = fix!(|fun, (&ref nVal, &ref xsVal)| match xsVal {
                VNil(_) => mnVal.dup(),
                VCons(_, box l, box x, box xs) => [l, x, xs, &fun.call((l, xs))]
                    .iter()
                    .fold(mcVal.dup(), |a, &b| vapp(&a, b))
                    .dup(),
                VNeutral(n) => VNeutral(box NVecElim(
                    box evalC(a, env),
                    box evalC(m, env),
                    box mnVal.dup(),
                    box mcVal.dup(),
                    box nVal.dup(),
                    box n.dup()
                )),
                _ => unreachable!(format!("unknown VecElim match {:?}", xsVal)),
            });
            frec.call((&evalC(n, env), &evalC(xs, env)))
        }
        Nil(a) => VNil(box evalC(a, env)),
        Cons(a, n, x, xs) => VCons(
            box evalC(a, env),
            box evalC(n, env),
            box evalC(x, env),
            box evalC(xs, env),
        ),
    }
}

#[allow(non_snake_case)]
fn evalC(trm: &TermC, env: &Env) -> Value {
    use {TermC::*, Value::*};
    match trm {
        Inf(i) => evalI(i, env),
        Lam(e) => {
            let env = env.clone();
            let e = e.dup();
            VLam(Rc::new(move |x| {
                evalC(&e, &[&[x.dup()], &env[..]].concat())
            }))
        }
    }
}

pub fn vapp(val: &Value, v: &Value) -> Value {
    use {Neutral::*, Value::*};
    match val {
        VLam(f) => f(v),
        VNeutral(n) => VNeutral(box NApp(box n.dup(), box v.dup())),
        _ => unreachable!(),
    }
}

type Result<T> = std::result::Result<T, String>;

#[allow(non_snake_case)]
pub fn typeI0(ctx: &Context, trm: &TermI) -> Result<Type> {
    typeI(0, ctx, trm)
}

#[allow(non_snake_case)]
fn typeI(i: Int, ctx: &Context, trm: &TermI) -> Result<Type> {
    use {Name::*, TermI::*, Value::*};
    match trm {
        Ann(e, p) => {
            typeC(i, ctx, p, &VStar)?;
            let t = evalC(p, &Env::new());
            typeC(i, ctx, e, &t)?;
            Ok(t.dup())
        }
        Star => Ok(VStar),
        Pi(p, p1) => {
            typeC(i, ctx, p, &VStar)?;
            let t = evalC(p, &Env::new());
            typeC(
                i + 1,
                &[&[(Local(i), t.dup())], &ctx[..]].concat(),
                &substC(0, &Free(box Local(i)), p1),
                &VStar,
            )?;
            Ok(VStar)
        }
        Free(x) => match lookup(ctx, x) {
            Some(t) => Ok(t.dup()),
            None => Err(format!("unk typevar {:?}", x)),
        },
        App(e, ep) => {
            let s = typeI(i, ctx, e)?;
            match s {
                VPi(box ref t, tp) => {
                    typeC(i, ctx, ep, t)?;
                    Ok(tp(&evalC(ep, &Env::new())))
                }
                _ => panic!("illegal application {:?}", (e, ep)),
            }
        }
        Nat => Ok(VStar),
        Zero => Ok(VNat),
        Succ(k) => {
            typeC(i, ctx, k, &VNat)?;
            Ok(VNat)
        }
        NatElim(m, mz, ms, k) => {
            typeC(i, ctx, m, &VPi(box VNat, Rc::new(|_| VStar)))?;
            let mVal = evalC(m, &Env::new());
            typeC(i, ctx, mz, &vapp(&mVal, &VZero))?;
            typeC(
                i,
                ctx,
                ms,
                &VPi(box VNat, {
                    let mVal = mVal.dup();
                    Rc::new(move |l| {
                        VPi(box vapp(&mVal, l), {
                            let l = l.dup();
                            let mVal = mVal.dup();
                            Rc::new(move |_| vapp(&mVal, &VSucc(l.b())))
                        })
                    })
                }),
            )?;
            typeC(i, ctx, k, &VNat)?;
            let kVal = evalC(k, &Env::new());
            Ok(vapp(&mVal, &kVal))
        }
        Vec(a, k) => {
            typeC(i, ctx, a, &VStar)?;
            typeC(i, ctx, k, &VNat)?;
            Ok(VStar)
        }
        Nil(a) => {
            typeC(i, ctx, a, &VStar)?;
            let aVal = evalC(a, &Env::new());
            Ok(VVec(box aVal, box VZero))
        }
        Cons(a, k, x, xs) => {
            typeC(i, ctx, a, &VStar)?;
            let aVal = evalC(a, &Env::new());
            typeC(i, ctx, k, &VNat)?;
            let kVal = evalC(k, &Env::new());
            typeC(i, ctx, x, &aVal)?;
            typeC(i, ctx, xs, &VVec(aVal.b(), kVal.b()))?;
            Ok(VVec(box aVal, box VSucc(box kVal)))
        }
        VecElim(a, m, mn, mc, k, vs) => {
            typeC(i, ctx, a, &VStar)?;
            let aVal = evalC(a, &Env::new());
            typeC(
                i,
                ctx,
                m,
                &VPi(
                    VNat.b(),
                    lam![{aVal} move |k| VPi(
                        VVec(aVal.b(), k.b()).b(),
                        lam!(|_| VStar),
                    )],
                ),
            )?;
            let mVal = evalC(m, &Env::new());
            typeC(
                i,
                ctx,
                mn,
                &[VZero, VNil(aVal.b())]
                    .iter()
                    .fold(mVal.dup(), |a, b| vapp(&a, &b)),
            )?;
            typeC(
                i,
                ctx,
                mc,
                &VPi(
                    VNat.b(),
                    lam![{aVal, mVal} move |l| VPi(
                        aVal.b(),
                        lam![{l, aVal, mVal} move |y| VPi(
                            VVec(aVal.b(), l.b()).b(),
                            lam![{l, y, aVal, mVal} move |ys| VPi(
                                [l.dup(), ys.dup()]
                                    .iter()
                                    .fold(mVal.dup(), |a, b| vapp(&a, &b))
                                    .b(),
                                lam![{l, y, ys, aVal, mVal} move |_| {
                                    [VSucc(l.b()), VCons(aVal.b(), l.b(), y.b(), ys.b())]
                                        .iter()
                                        .fold(mVal.dup(), |a, b| vapp(&a, &b))
                                }],
                            )]
                        )],
                    )],
                ),
            )?;
            typeC(i, ctx, k, &VNat)?;
            let kVal = evalC(k, &Env::new());
            typeC(i, ctx, vs, &VVec(box aVal.dup(), box kVal.dup()))?;
            let vsVal = evalC(vs, &Env::new());
            Ok([kVal, vsVal].iter().fold(mVal, |a, b| vapp(&a, &b)))
        }
        _ => unreachable!("unhandled {:?}", trm),
    }
}

#[allow(non_snake_case)]
fn typeC(i: Int, ctx: &Context, trm: &TermC, typ: &Type) -> Result<()> {
    use {Name::*, TermC::*, TermI::*, Value::*};
    match (trm, typ) {
        (Inf(e), _) => {
            let v1 = typeI(i, ctx, e)?;
            if quote0(typ) != quote0(&v1) {
                return Err(format!("type mismatch {:?}", (typ, v1)));
            }
            Ok(())
        }
        (Lam(e), VPi(t, tp)) => typeC(
            i + 1,
            &[&[(Local(i), t.dup())], &ctx[..]].concat(),
            &substC(0, &Free(box Local(i)), e),
            &tp(&vfree(Local(i))),
        ),
        _ => unreachable!(),
    }
}

pub fn quote0(v: &Value) -> TermC {
    quote(0, v)
}

fn quote(i: Int, v: &Value) -> TermC {
    use {Name::*, TermC::*, TermI::*, Value::*};
    match v {
        VLam(f) => Lam(box quote(i + 1, &f(&vfree(Quote(i))))),
        VStar => Inf(box Star),
        VPi(v, f) => Inf(box Pi(
            box quote(i, v),
            box quote(i + 1, &f(&vfree(Quote(i)))),
        )),
        VNeutral(n) => Inf(box neutralQuote(i, n)),
        VNat => Inf(box Nat),
        VZero => Inf(box Zero),
        VSucc(v) => Inf(box Succ(box quote(i, v))),
        VNil(a) => Inf(box Nil(quote(i, a).b())),
        VVec(a, n) => Inf(box Vec(box quote(i, a), box quote(i, n))),
        VCons(a, n, x, xs) => Inf(box Cons(
            box quote(i, a),
            box quote(i, n),
            box quote(i, x),
            box quote(i, xs),
        )),
    }
}

#[allow(non_snake_case)]
fn substC(i: Int, ti: &TermI, tc: &TermC) -> TermC {
    use TermC::*;
    match tc {
        Inf(e) => Inf(box substI(i, ti, e)),
        Lam(e) => Lam(box substC(i + 1, ti, e)),
    }
}

#[allow(non_snake_case)]
fn substI(i: Int, r: &TermI, ti: &TermI) -> TermI {
    use TermI::*;
    match ti {
        Ann(e, t) => Ann(substC(i, r, e).b(), t.b()),
        Star => Star,
        Pi(t, tp) => Pi(substC(i, r, t).b(), substC(i + 1, r, tp).b()),
        &Bound(j) => match j {
            j if i == j => r.dup(),
            j => Bound(j),
        },
        Free(y) => Free(y.b()),
        App(e, ep) => App(substI(i, r, e).b(), substC(i, r, ep).b()),
        Nat => Nat,
        NatElim(m, mz, ms, n) => NatElim(
            substC(i, r, m).b(),
            substC(i, r, mz).b(),
            substC(i, r, ms).b(),
            substC(i, r, n).b(),
        ),
        Zero => Zero,
        Succ(n) => Succ(substC(i, r, n).b()),
        Vec(a, n) => Vec(substC(i, r, a).b(), substC(i, r, n).b()),
        VecElim(a, m, mn, mc, n, xs) => VecElim(
            substC(i, r, a).b(),
            substC(i, r, m).b(),
            substC(i, r, mn).b(),
            substC(i, r, mc).b(),
            substC(i, r, n).b(),
            substC(i, r, xs).b(),
        ),
        Nil(a) => Nil(substC(i, r, a).b()),
        Cons(a, n, x, xs) => Cons(
            substC(i, r, a).b(),
            substC(i, r, n).b(),
            substC(i, r, x).b(),
            substC(i, r, xs).b(),
        ),
    }
}

#[allow(non_snake_case)]
fn neutralQuote(i: Int, n: &Neutral) -> TermI {
    use {Neutral::*, TermC::*, TermI::*};
    match n {
        NFree(x) => boundfree(i, x),
        NApp(n, v) => App(box neutralQuote(i, n), box quote(i, v)),
        NNatElim(a, n, x, xs) => NatElim(
            quote(i, a).b(),
            quote(i, n).b(),
            quote(i, x).b(),
            Inf(neutralQuote(i, xs).b()).b(),
        ),
        NVecElim(a, m, mn, mc, n, xs) => VecElim(
            quote(i, a).b(),
            quote(i, m).b(),
            quote(i, mn).b(),
            quote(i, mc).b(),
            quote(i, n).b(),
            Inf(neutralQuote(i, xs).b()).b(),
        ),
    }
}

fn boundfree(i: Int, n: &Name) -> TermI {
    use {Name::*, TermI::*};
    match n {
        Quote(k) => Bound(i - k - 1),
        x => Free(x.b()),
    }
}

pub fn vapply(f: &Value, args: &Vec<Value>) -> Value {
    let mut f = f.dup();
    for arg in args {
        f = vapp(&f, arg)
    }
    f
}
