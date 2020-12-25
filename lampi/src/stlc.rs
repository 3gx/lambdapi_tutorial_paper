type Int = i32;
use std::rc::Rc;

pub fn test() -> i32 {
    42
}

/*
#[derive(ADT)]
enum TermI {
    Ann(TermC, Type),
    Bound(Int),
    Free(Name),
    App(TermI, TermC),
};
 */

pub trait Boxed: Sized + Clone {
    fn b(self: &Self) -> Box<Self> {
        box self.clone()
    }
    fn dup(self: &Self) -> Self {
        self.clone()
    }
}
// ---------------------------------------------------------------------------

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum TermI {
    Ann(Box<TermC>, Box<Type>),
    Bound(Int),
    Free(Box<Name>),
    App(Box<TermI>, Box<TermC>),
}
impl Boxed for TermI {}

// ---------------------------------------------------------------------------

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum TermC {
    Inf(Box<TermI>),
    Lam(Box<TermC>),
}
impl Boxed for TermC {}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Name {
    Global(String),
    Local(Int),
    Quote(Int),
}
impl Boxed for Name {}

// ---------------------------------------------------------------------------

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Type {
    TFree(Box<Name>),
    Fun(Box<Type>, Box<Type>),
}
impl Boxed for Type {}

// ---------------------------------------------------------------------------

#[derive(Clone)]
pub enum Value {
    VLam(Rc<dyn Fn(&Value) -> Value>),
    VNeutral(Box<Neutral>),
}
impl Boxed for Value {}

// ---------------------------------------------------------------------------

#[derive(Clone)]
pub enum Neutral {
    NFree(Box<Name>),
    NApp(Box<Neutral>, Box<Value>),
}
impl Boxed for Neutral {}

// ---------------------------------------------------------------------------

fn vfree(n: Name) -> Value {
    Value::VNeutral(Neutral::NFree(n.b()).b())
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Kind {
    Star,
}

// ---------------------------------------------------------------------------

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Info {
    HasKind(Box<Kind>),
    HasType(Box<Type>),
}
impl Boxed for Info {}

// ---------------------------------------------------------------------------

use std::collections::VecDeque;
type Env = VecDeque<Value>;

#[allow(non_snake_case)]
pub fn evalI(trm: &TermI, env: &Env) -> Value {
    match trm {
        TermI::Ann(e, _) => evalC(&e, env),
        TermI::Free(x) => vfree(x.dup()),
        &TermI::Bound(i) => env[i as usize].dup(),
        TermI::App(e, ep) => vapp(&evalI(&e, env), &evalC(&ep, env)),
    }
}

#[allow(non_snake_case)]
pub fn evalC(trm: &TermC, env: &Env) -> Value {
    match trm {
        TermC::Inf(i) => evalI(i, env),
        TermC::Lam(e) => {
            let env = env.clone();
            let e = e.dup();
            Value::VLam(Rc::new(move |x| {
                let mut env = env.clone();
                env.push_front(x.dup());
                evalC(&e, &env)
            }))
        }
    }
}

pub fn vapp(v1: &Value, v: &Value) -> Value {
    match v1 {
        Value::VLam(f) => f(v),
        Value::VNeutral(n) => Value::VNeutral(Neutral::NApp(n.b(), v.b()).b()),
    }
}

type Ctx = VecDeque<(Name, Info)>;
type Result<T> = std::result::Result<T, String>;

fn lookup<'a, 'b>(c: &'a Ctx, n: &'b Name) -> Option<&'a Info> {
    if let Some((_, i)) = c.iter().find(|x| x.0 == *n) {
        Some(i)
    } else {
        None
    }
}

#[allow(non_snake_case)]
fn kindC(ctx: &Ctx, t: &Type, k: &Kind) -> Result<()> {
    match (t, k) {
        (Type::TFree(x), Kind::Star) => {
            if let Some(x) = lookup(ctx, x) {
                match x {
                    Info::HasKind(box Kind::Star) => Ok(()),
                    _ => panic!("unhandled case {:?}", x),
                }
            } else {
                Err(format!("unk var identifier {:?}", x))
            }
        }
        (Type::Fun(k, k1), Kind::Star) => {
            kindC(ctx, k, &Kind::Star)?;
            kindC(ctx, k1, &Kind::Star)
        }
    }
}

#[allow(non_snake_case)]
pub fn typeI0(c: &Ctx, term: &TermI) -> Result<Type> {
    typeI(0, c, term)
}

#[allow(non_snake_case)]
pub fn typeI(i: Int, c: &Ctx, trm: &TermI) -> Result<Type> {
    match trm {
        TermI::Ann(e, t) => {
            kindC(c, &t, &Kind::Star)?;
            typeC(i, c, &e, &t)?;
            Ok(t.dup())
        }
        TermI::Free(x) => {
            if let Some(x) = lookup(c, &x) {
                match x {
                    Info::HasType(t) => Ok(t.dup()),
                    _ => panic!("unhandled case {:?}", x),
                }
            } else {
                Err(format!("unk type identifier {:?}", x))
            }
        }
        TermI::App(e, ep) => {
            let s = typeI(i, c, &e)?;
            match s {
                Type::Fun(t, tp) => {
                    typeC(i, c, &ep, &t)?;
                    Ok(tp.dup())
                }
                _ => Err(format!(" illegal application {:?}", (e, ep))),
            }
        }
        _ => panic!("unhandled case {:?}", trm),
    }
}

#[allow(non_snake_case)]
pub fn typeC(i: Int, c: &Ctx, term: &TermC, typ: &Type) -> Result<()> {
    match (term, typ) {
        (TermC::Inf(e), _) => {
            let tp = &typeI(i, c, e)?;
            if typ != tp {
                return Err(format!("[inf] type mismatch {:?}", (typ, tp)));
            }
            Ok(())
        }
        (TermC::Lam(e), Type::Fun(t, tp)) => {
            let mut c = c.clone();
            c.push_front((Name::Local(i), Info::HasType(t.b())));
            let s = substC(0, &TermI::Free(Name::Local(i).b()), e);
            typeC(i + 1, &c, &s, tp)
        }
        _ => Err(format!("oops, type mismatch {:?}", (term, typ))),
    }
}

#[allow(non_snake_case)]
fn substI(i: Int, r: &TermI, t: &TermI) -> TermI {
    match t {
        TermI::Ann(e, t) => TermI::Ann(substC(i, r, e).b(), t.b()),
        &TermI::Bound(j) => {
            if i == j {
                r.dup()
            } else {
                TermI::Bound(j)
            }
        }
        TermI::Free(y) => TermI::Free(y.b()),
        TermI::App(e, ep) => TermI::App(substI(i, r, &e).b(), substC(i, r, &ep).b()),
    }
}

#[allow(non_snake_case)]
fn substC(i: Int, r: &TermI, t: &TermC) -> TermC {
    match t {
        TermC::Inf(e) => TermC::Inf(substI(i, r, e).b()),
        TermC::Lam(e) => TermC::Lam(substC(i + 1, r, e).b()),
    }
}

pub fn quote0(v: &Value) -> TermC {
    quote(0, v)
}

fn quote(i: Int, v: &Value) -> TermC {
    match v {
        Value::VLam(f) => TermC::Lam(quote(i + 1, &f(&vfree(Name::Quote(i)))).b()),
        Value::VNeutral(n) => TermC::Inf(neutralQuote(i, n).b()),
    }
}

#[allow(non_snake_case)]
fn neutralQuote(i: Int, n: &Neutral) -> TermI {
    match n {
        Neutral::NFree(x) => boundfree(i, x),
        Neutral::NApp(n, v) => TermI::App(neutralQuote(i, n).b(), quote(i, v).b()),
    }
}

fn boundfree(i: Int, n: &Name) -> TermI {
    match n {
        Name::Quote(k) => TermI::Bound(i - k - 1),
        _ => TermI::Free(n.b()),
    }
}

