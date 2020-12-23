type Int = i32;
use std::rc::Rc;

pub fn test() -> i32 {
    42
}

type BBox<T> = Rc<T>;

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TermI(BBox<TermIKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum TermIKind {
    Ann(TermC, Type),
    Bound(Int),
    Free(Name),
    App(TermI, TermC),
}

impl TermI {
    fn kind(&self) -> &TermIKind {
        return &*self.0;
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TermC(BBox<TermCKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum TermCKind {
    Inf(TermI),
    Lam(TermC),
}
impl TermC {
    fn kind(&self) -> &TermCKind {
        return &*self.0;
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Name(BBox<NameKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum NameKind {
    Global(String),
    Local(Int),
    Quote(Int),
}

impl Name {
    fn kind(&self) -> &NameKind {
        return &*self.0;
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Type(BBox<TypeKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum TypeKind {
    Free(Name),
    Fun(Type, Type),
}

impl Type {
    fn kind(&self) -> &TypeKind {
        return &*self.0;
    }
}

#[derive(Clone)]
pub struct Value(BBox<ValueKind>);

#[derive(Clone)]
enum ValueKind {
    Lam(BBox<dyn Fn(&Value) -> Value>),
    Neutral(Neutral),
}

impl Value {
    fn kind(&self) -> &ValueKind {
        return &*self.0;
    }
}

impl Value {
    #![allow(non_snake_case)]
    fn new(kind: ValueKind) -> Value {
        Value(BBox::new(kind))
    }
    fn Lam(v: BBox<dyn Fn(&Value) -> Value>) -> Value {
        Value::new(ValueKind::Lam(v))
    }
    fn Neutral(n: Neutral) -> Value {
        Value::new(ValueKind::Neutral(n))
    }
    fn clone(&self) -> Value {
        Value(BBox::clone(&self.0))
    }
}

#[derive(Clone)]
struct Neutral(BBox<NeutralKind>);

#[derive(Clone)]
enum NeutralKind {
    Free(Name),
    App(Neutral, Value),
}

impl Neutral {
    #![allow(non_snake_case)]
    fn new(kind: NeutralKind) -> Neutral {
        Neutral(BBox::new(kind))
    }

    fn Free(n: Name) -> Neutral {
        Neutral::new(NeutralKind::Free(n))
    }

    fn App(n: Neutral, v: Value) -> Neutral {
        Neutral::new(NeutralKind::App(n, v))
    }
    fn kind(&self) -> &NeutralKind {
        return &self.0;
    }
}

fn vfree(n: &Name) -> Value {
    Value::Neutral(Neutral::Free(n.clone()))
}

use std::collections::VecDeque;
type Env = VecDeque<Value>;

#[allow(non_snake_case)]
pub fn evalI(term: &TermI, env: &Env) -> Value {
    match term.kind() {
        TermIKind::Ann(e, _) => evalC(e, env),
        TermIKind::Free(x) => vfree(x),
        TermIKind::Bound(i) => env[*i as usize].clone(),
        TermIKind::App(e, ep) => {
            let v1 = &evalI(e, env);
            let v2 = &evalC(ep, env);
            vapp(v1, v2)
        }
    }
}

#[allow(non_snake_case)]
pub fn evalC(term: &TermC, env: &Env) -> Value {
    match term.kind() {
        TermCKind::Inf(i) => evalI(i, env),
        TermCKind::Lam(e) => {
            let env = env.clone();
            let e = e.clone();
            Value::Lam(BBox::new(move |x| {
                let mut env = env.clone();
                env.push_front(x.clone());
                evalC(&e, &env)
            }))
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
enum Kind {
    Star,
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct Info(BBox<InfoKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum InfoKind {
    HasKind(Kind),
    HasType(Type),
}

impl Info {
    #![allow(non_snake_case)]
    fn kind(&self) -> &InfoKind {
        &self.0
    }
    fn new(kind: InfoKind) -> Info {
        return Info(BBox::new(kind));
    }
    fn HasKind(kind: Kind) -> Info {
        Info::new(InfoKind::HasKind(kind))
    }
    fn HasType(typ: Type) -> Info {
        Info::new(InfoKind::HasType(typ))
    }
}

pub fn vapp(v1: &Value, v: &Value) -> Value {
    match v1.kind() {
        ValueKind::Lam(f) => f(v),
        ValueKind::Neutral(n) => Value::Neutral(Neutral::App(n.clone(), v.clone())),
    }
}

type Ctx = Vec<(Name, Info)>;
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
        (TypeKind::Free(x), Kind::Star) => {
            if let Some(x) = lookup(ctx, x) {
                match x.kind() {
                    InfoKind::HasKind(Kind::Star) => Ok(()),
                    _ => panic!("unhandled case {:?}", x),
                }
            } else {
                Err(format!("unk var identifier {:?}", x))
            }
        }
        (TypeKind::Fun(k, k1), Kind::Star) => {
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
        TermIKind::Ann(e, t) => {
            kindC(c, t, &Kind::Star)?;
            typeC(i, c, e, t)?;
            Ok(t.clone())
        }
        TermIKind::Free(x) => {
            if let Some(x) = lookup(c, x) {
                match x.kind() {
                    InfoKind::HasType(t) => Ok(t.clone()),
                    _ => panic!("unhandled case {:?}", x),
                }
            } else {
                Err(format!("unk type identifier {:?}", x))
            }
        }
        TermIKind::App(e, e1) => {
            unimplemented!()
        }
        _ => panic!("unhandled case {:?}", term),
    }
}

#[allow(non_snake_case)]
fn typeC(i: Int, c: &Ctx, term: &TermC, typ: &Type) -> Result<()> {
    unimplemented!()
}
