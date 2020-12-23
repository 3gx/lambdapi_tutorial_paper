type Int = i32;
use std::rc::Rc;

pub fn test() -> i32 {
    42
}

type BBox<T> = Rc<T>;
/*
#[derive(ADT)]
enum TermI {
    Ann(TermC, Type),
    Bound(Int),
    Free(Name),
    App(TermI, TermC),
};
 */

// ---------------------------------------------------------------------------

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TermI(BBox<kTermI>);

#[derive(Clone, Eq, PartialEq, Debug)]
#[allow(non_camel_case_types)]
enum kTermI {
    Ann(TermC, Type),
    Bound(Int),
    Free(Name),
    App(TermI, TermC),
}

impl TermI {
    #![allow(non_snake_case)]
    fn kind(&self) -> &kTermI {
        return &*self.0;
    }
    fn Ann(trm: TermC, typ: Type) -> TermI {
        TermI(BBox::new(kTermI::Ann(trm, typ)))
    }
    fn Bound(i: Int) -> TermI {
        TermI(BBox::new(kTermI::Bound(i)))
    }
    fn Free(n: Name) -> TermI {
        TermI(BBox::new(kTermI::Free(n)))
    }
    fn App(ti: TermI, tc: TermC) -> TermI {
        TermI(BBox::new(kTermI::App(ti, tc)))
    }
}

// ---------------------------------------------------------------------------

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TermC(BBox<kTermC>);

#[allow(non_camel_case_types)]
#[derive(Clone, Eq, PartialEq, Debug)]
enum kTermC {
    Inf(TermI),
    Lam(TermC),
}

impl TermC {
    #![allow(non_snake_case)]
    fn kind(&self) -> &kTermC {
        return &*self.0;
    }
    fn Inf(ti: TermI) -> TermC {
        TermC(BBox::new(kTermC::Inf(ti)))
    }
    fn Lam(tc: TermC) -> TermC {
        TermC(BBox::new(kTermC::Lam(tc)))
    }
}

// ---------------------------------------------------------------------------

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Name(BBox<kName>);

#[derive(Clone, Eq, PartialEq, Debug)]
#[allow(non_camel_case_types)]
enum kName {
    Global(String),
    Local(Int),
    Quote(Int),
}

impl Name {
    #![allow(non_snake_case)]
    fn kind(&self) -> &kName {
        return &*self.0;
    }
    fn Global(s: String) -> Name {
        Name(BBox::new(kName::Global(s)))
    }
    fn Local(i: Int) -> Name {
        Name(BBox::new(kName::Local(i)))
    }
    fn Quote(i: Int) -> Name {
        Name(BBox::new(kName::Quote(i)))
    }
}

// ---------------------------------------------------------------------------

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Type(BBox<kType>);

#[derive(Clone, Eq, PartialEq, Debug)]
#[allow(non_camel_case_types)]
enum kType {
    TFree(Name),
    Fun(Type, Type),
}

impl Type {
    #![allow(non_snake_case)]
    fn kind(&self) -> &kType {
        return &*self.0;
    }
    fn TFree(n: Name) -> Type {
        Type(BBox::new(kType::TFree(n)))
    }
    fn Fun(t1: Type, t2: Type) -> Type {
        Type(BBox::new(kType::Fun(t1, t2)))
    }
}

// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct Value(BBox<kValue>);

#[derive(Clone)]
#[allow(non_camel_case_types)]
enum kValue {
    VLam(BBox<dyn Fn(&Value) -> Value>),
    VNeutral(Neutral),
}

impl Value {
    #![allow(non_snake_case)]
    fn kind(&self) -> &kValue {
        return &*self.0;
    }
    fn VLam(v: BBox<dyn Fn(&Value) -> Value>) -> Value {
        Value(BBox::new(kValue::VLam(v)))
    }
    fn VNeutral(n: Neutral) -> Value {
        Value(BBox::new(kValue::VNeutral(n)))
    }
}

// ---------------------------------------------------------------------------

#[derive(Clone)]
struct Neutral(BBox<kNeutral>);

#[derive(Clone)]
#[allow(non_camel_case_types)]
enum kNeutral {
    NFree(Name),
    NApp(Neutral, Value),
}

impl Neutral {
    #![allow(non_snake_case)]
    fn kind(&self) -> &kNeutral {
        return &self.0;
    }

    fn NFree(n: Name) -> Neutral {
        Neutral(BBox::new(kNeutral::NFree(n)))
    }

    fn NApp(n: Neutral, v: Value) -> Neutral {
        Neutral(BBox::new(kNeutral::NApp(n, v)))
    }
}

// ---------------------------------------------------------------------------

fn vfree(n: Name) -> Value {
    Value::VNeutral(Neutral::NFree(n))
}

#[derive(Clone, Eq, PartialEq, Debug)]
enum Kind {
    Star,
}

// ---------------------------------------------------------------------------

#[derive(Clone, Eq, PartialEq, Debug)]
struct Info(BBox<kInfo>);

#[derive(Clone, Eq, PartialEq, Debug)]
#[allow(non_camel_case_types)]
enum kInfo {
    HasKind(Kind),
    HasType(Type),
}

impl Info {
    #![allow(non_snake_case)]
    fn kind(&self) -> &kInfo {
        &self.0
    }
    fn HasKind(kind: Kind) -> Info {
        Info(BBox::new(kInfo::HasKind(kind)))
    }
    fn HasType(typ: Type) -> Info {
        Info(BBox::new(kInfo::HasType(typ)))
    }
}

// ---------------------------------------------------------------------------

use std::collections::VecDeque;
type Env = VecDeque<Value>;

#[allow(non_snake_case)]
pub fn evalI(term: &TermI, env: &Env) -> Value {
    match term.kind() {
        kTermI::Ann(e, _) => evalC(e, env),
        kTermI::Free(x) => vfree(x.clone()),
        kTermI::Bound(i) => env[*i as usize].clone(),
        kTermI::App(e, ep) => vapp(&evalI(e, env), &evalC(ep, env)),
    }
}

#[allow(non_snake_case)]
pub fn evalC(term: &TermC, env: &Env) -> Value {
    match term.kind() {
        kTermC::Inf(i) => evalI(i, env),
        kTermC::Lam(e) => {
            let env = env.clone();
            let e = e.clone();
            Value::VLam(BBox::new(move |x| {
                let mut env = env.clone();
                env.push_front(x.clone());
                evalC(&e, &env)
            }))
        }
    }
}

pub fn vapp(v1: &Value, v: &Value) -> Value {
    match v1.kind() {
        kValue::VLam(f) => f(v),
        kValue::VNeutral(n) => Value::VNeutral(Neutral::NApp(n.clone(), v.clone())),
    }
}

type Ctx = VecDeque<(Name, Info)>;
type Result<T> = std::result::Result<T, String>;

fn lookup<'a, 'b>(c: &'a Ctx, n: &'b Name) -> Option<&'a Info> {
    if let Some((n, i)) = c.iter().find(|x| x.0 == *n) {
        Some(i)
    } else {
        None
    }
}

#[allow(non_snake_case)]
fn kindC(ctx: &Ctx, t: &Type, k: &Kind) -> Result<()> {
    match (t.kind(), k) {
        (kType::TFree(x), Kind::Star) => {
            if let Some(x) = lookup(ctx, x) {
                match x.kind() {
                    kInfo::HasKind(Kind::Star) => Ok(()),
                    _ => panic!("unhandled case {:?}", x),
                }
            } else {
                Err(format!("unk var identifier {:?}", x))
            }
        }
        (kType::Fun(k, k1), Kind::Star) => {
            kindC(ctx, k, &Kind::Star)?;
            kindC(ctx, k1, &Kind::Star)
        }
    }
}

#[allow(non_snake_case)]
fn typeI0(c: &Ctx, term: &TermI) -> Result<Type> {
    typeI(0, c, term)
}

#[allow(non_snake_case)]
fn typeI(i: Int, c: &Ctx, term: &TermI) -> Result<Type> {
    match term.kind() {
        kTermI::Ann(e, t) => {
            kindC(c, t, &Kind::Star)?;
            typeC(i, c, e, t)?;
            Ok(t.clone())
        }
        kTermI::Free(x) => {
            if let Some(x) = lookup(c, x) {
                match x.kind() {
                    kInfo::HasType(t) => Ok(t.clone()),
                    _ => panic!("unhandled case {:?}", x),
                }
            } else {
                Err(format!("unk type identifier {:?}", x))
            }
        }
        kTermI::App(e, ep) => {
            let s = typeI(i, c, e)?;
            match s.kind() {
                kType::Fun(t, tp) => {
                    typeC(i, c, ep, t)?;
                    Ok(tp.clone())
                }
                _ => Err(format!(" illegal application {:?}", (e, ep))),
            }
        }
        _ => panic!("unhandled case {:?}", term),
    }
}

#[allow(non_snake_case)]
fn typeC(i: Int, c: &Ctx, term: &TermC, typ: &Type) -> Result<()> {
    match (term.kind(), typ.kind()) {
        (kTermC::Inf(e), _) => {
            let tp = &typeI(i, c, e)?;
            if typ != tp {
                return Err(format!("[inf] type mismatch {:?}", (typ, tp)));
            }
            Ok(())
        }
        (kTermC::Lam(e), kType::Fun(t, tp)) => {
            let mut c = c.clone();
            c.push_front((Name::Local(i), Info::HasType(t.clone())));
            let s = substC(0, &TermI::Free(Name::Local(i)), e);
            typeC(i + 1, &c, &s, tp)
        }
        _ => Err(format!("oops, type mismatch {:?}", (term, typ))),
    }
}

#[allow(non_snake_case)]
fn substI(i: Int, r: &TermI, t: &TermI) -> TermI {
    match t.kind() {
        kTermI::Ann(e, t) => TermI::Ann(substC(i, r, e), t.clone()),
        kTermI::Bound(j) => {
            if i == *j {
                r.clone()
            } else {
                TermI::Bound(*j)
            }
        }
        kTermI::Free(y) => TermI::Free(y.clone()),
        kTermI::App(e, ep) => TermI::App(substI(i, r, e), substC(i, r, ep)),
    }
}

#[allow(non_snake_case)]
fn substC(i: Int, r: &TermI, t: &TermC) -> TermC {
    match t.kind() {
        kTermC::Inf(e) => TermC::Inf(substI(i, r, e)),
        kTermC::Lam(e) => TermC::Lam(substC(i + 1, r, e)),
    }
}
