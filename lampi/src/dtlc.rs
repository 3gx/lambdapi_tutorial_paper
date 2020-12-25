use std::rc::Rc;

type Int = i32;

trait Boxed: Sized + Clone {
    fn b(self: &Self) -> Box<Self> {
        box self.clone()
    }
    fn dup(self: &Self) -> Self {
        self.clone()
    }
}

// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum TermI {
    Ann(Box<TermC>, Box<TermC>),
    Star,
    Pi(Box<TermC>, Box<TermC>),
    Bound(Int),
    Free(Box<Name>),
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
impl Boxed for TermI {}

// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum TermC {
    Inf(Box<TermI>),
    Lam(Box<TermC>),
}
impl Boxed for TermC {}

// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum Name {
    Global(String),
    Local(Int),
    Quote(Int),
}
impl Boxed for Name {}

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
impl Boxed for Value {}

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
impl Boxed for Neutral {}

// ---------------------------------------------------------------------------

type Type = Value;

fn vfree(n: Name) -> Value {
    Value::VNeutral(box Neutral::NFree(box n))
}

type Env = Vec<Value>;
type Context = Vec<(Name, Type)>;
