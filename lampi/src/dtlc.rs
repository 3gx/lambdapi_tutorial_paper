use std::rc::Rc;

type Int = i32;

trait Dup: Sized + Clone {
    //    fn b(self: &Self) -> Box<Self> {
    //       box self.clone()
    //    }
    fn dup(self: &Self) -> Self {
        self.clone()
    }
}

struct Fix1<'a, T, U> {
    f: &'a dyn Fn(&Fix1<'a, T, U>, T) -> U,
}

impl<'a, T, U> Fix1<'a, T, U> {
    fn call(&self, x: T) -> U {
        (self.f)(self, x)
    }
}

macro_rules! fix1 {
    ($e:expr) => {
        Fix1 { f: &$e }
    };
}

// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
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

#[derive(Clone, Debug)]
pub enum TermC {
    Inf(Box<TermI>),
    Lam(Box<TermC>),
}
impl Dup for TermC {}

// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
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
            Value::VLam(_) => write!(f, "VLam(<fun>)"),
            Value::VStar => write!(f, "VStar"),
            Value::VPi(v, _) => write!(f, "VPi({:?},<fun>)", v),
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

type Env = Vec<Value>;
type Context = Vec<(Name, Type)>;

#[allow(non_snake_case)]
pub fn evalI(trm: &TermI, env: &Env) -> Value {
    use {Neutral::*, TermI::*, Value::*};
    match trm {
        Ann(e, _) => evalC(e, env),
        Star => VStar,
        Pi(t, tp) => VPi(box evalC(t, env), {
            let tp = tp.dup();
            let env = env.clone();
            Rc::new(move |x| evalC(&tp, &[&[x.dup()], &env[..]].concat()))
        }),
        Free(x) => vfree(x.dup()),
        Bound(i) => env[*i as usize].dup(),
        App(e, ep) => vapp(&evalI(e, env), &evalC(ep, env)),
        Nat => VNat,
        Zero => VZero,
        Succ(k) => VSucc(box evalC(k, env)),
        NatElim(box m, mz, ms, box k) => {
            let mzVal = evalC(mz, env);
            let msVal = evalC(ms, env);
            fix1!(|rec, &ref kVal| match kVal {
                VZero => mzVal.dup(),
                VSucc(box ref l) => vapp(&vapp(&msVal, l), &rec.call(l)),
                VNeutral(box k) => VNeutral(box NNatElim(
                    box evalC(m, env),
                    box mzVal.dup(),
                    box msVal.dup(),
                    box k.dup(),
                )),
                _ => unreachable!(format!("unknown natElim match {:?}", kVal)),
            }).call(&evalC(k,env))
        },
        Vec(a,n) => VVec(box evalC(a,env), box evalC(n,env)),
        VecElim(a,m,mn,mc,n,xs) => {
            let mnVal = evalC(mn,env);
            let mcVal = evalC(mc,env);
            fix1!(|rec, (&ref nVal, &ref xsVal)| match xsVal {
                VNil(_) => mnVal.dup(),
                VCons(_, l, x,xs) => unimplemented!(),
                VNeutral(n) => unimplemented!(),
                _ => unreachable!(format!("unknown VecElim match {:?}", xsVal))
            }).call((&evalC(n,env), &evalC(xs,env)))
        }
        _ => unreachable!(),
    }
}

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

fn vapp(val: &Value, v: &Value) -> Value {
    use {Neutral::*, Value::*};
    match val {
        VLam(f) => f(v),
        VNeutral(n) => VNeutral(box NApp(box n.dup(), box v.dup())),
        _ => unreachable!(),
    }
}
