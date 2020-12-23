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
    fn new(kind: kTermI) -> TermI {
        TermI(BBox::new(kind))
    }
    fn kind(&self) -> &kTermI {
        return &*self.0;
    }
}

impl TermI {
    #![allow(non_snake_case)]
    fn Ann(trm: TermC, typ: Type) -> TermI {
        TermI::new(kTermI::Ann(trm, typ))
    }
    fn Bound(i: Int) -> TermI {
        TermI::new(kTermI::Bound(i))
    }
    fn Free(n: Name) -> TermI {
        TermI::new(kTermI::Free(n))
    }
    fn App(ti: TermI, tc: TermC) -> TermI {
        TermI::new(kTermI::App(ti, tc))
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
    fn new(kind: kTermC) -> TermC {
        TermC(BBox::new(kind))
    }
    fn kind(&self) -> &kTermC {
        return &*self.0;
    }
}
impl TermC {
    #![allow(non_snake_case)]
    fn Inf(ti: TermI) -> TermC {
        TermC::new(kTermC::Inf(ti))
    }
    fn Lam(tc: TermC) -> TermC {
        TermC::new(kTermC::Lam(tc))
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
    fn new(kind: kName) -> Name {
        Name(BBox::new(kind))
    }
    fn kind(&self) -> &kName {
        return &*self.0;
    }
}
impl Name {
    #![allow(non_snake_case)]
    fn Global(s: String) -> Name {
        Name::new(kName::Global(s))
    }
    fn Local(i: Int) -> Name {
        Name::new(kName::Local(i))
    }
    fn Quote(i: Int) -> Name {
        Name::new(kName::Quote(i))
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
    fn new(kind: kType) -> Type {
        Type(BBox::new(kind))
    }
    fn kind(&self) -> &kType {
        return &*self.0;
    }
}

impl Type {
    fn TFree(n: Name) -> Type {
        Type::new(kType::TFree(n))
    }
    fn Fun(t1: Type, t2: Type) -> Type {
        Type::new(kType::Fun(t1, t2))
    }
}

// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct Value(BBox<kValue>);

#[derive(Clone)]
#[allow(non_camel_case_types)]
enum kValue {
    Lam(BBox<dyn Fn(&Value) -> Value>),
    Neutral(Neutral),
}

impl Value {
    fn new(k: kValue) -> Value {
        Value(BBox::new(k))
    }
    fn kind(&self) -> &kValue {
        return &*self.0;
    }
}

impl Value {
    #![allow(non_snake_case)]
    fn Lam(v: BBox<dyn Fn(&Value) -> Value>) -> Value {
        Value::new(kValue::Lam(v))
    }
    fn Neutral(n: Neutral) -> Value {
        Value::new(kValue::Neutral(n))
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
    fn new(kind: kNeutral) -> Neutral {
        Neutral(BBox::new(kind))
    }
    fn kind(&self) -> &kNeutral {
        return &self.0;
    }
}
impl Neutral {
    #![allow(non_snake_case)]

    fn NFree(n: Name) -> Neutral {
        Neutral::new(kNeutral::NFree(n))
    }

    fn App(n: Neutral, v: Value) -> Neutral {
        Neutral::new(kNeutral::NApp(n, v))
    }
}

// ---------------------------------------------------------------------------

fn vfree(n: &Name) -> Value {
    Value::Neutral(Neutral::NFree(n.clone()))
}

use std::collections::VecDeque;
type Env = VecDeque<Value>;

#[allow(non_snake_case)]
pub fn evalI(term: &TermI, env: &Env) -> Value {
    match term.kind() {
        kTermI::Ann(e, _) => evalC(e, env),
        kTermI::Free(x) => vfree(x),
        kTermI::Bound(i) => env[*i as usize].clone(),
        kTermI::App(e, ep) => {
            let v1 = &evalI(e, env);
            let v2 = &evalC(ep, env);
            vapp(v1, v2)
        }
    }
}

#[allow(non_snake_case)]
pub fn evalC(term: &TermC, env: &Env) -> Value {
    match term.kind() {
        kTermC::Inf(i) => evalI(i, env),
        kTermC::Lam(e) => {
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
        kValue::Lam(f) => f(v),
        kValue::Neutral(n) => Value::Neutral(Neutral::App(n.clone(), v.clone())),
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
        (kType::TFree(x), Kind::Star) => {
            if let Some(x) = lookup(ctx, x) {
                match x.kind() {
                    InfoKind::HasKind(Kind::Star) => Ok(()),
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
                    InfoKind::HasType(t) => Ok(t.clone()),
                    _ => panic!("unhandled case {:?}", x),
                }
            } else {
                Err(format!("unk type identifier {:?}", x))
            }
        }
        kTermI::App(e, e1) => {
            unimplemented!()
        }
        _ => panic!("unhandled case {:?}", term),
    }
}

#[allow(non_snake_case)]
fn typeC(i: Int, c: &Ctx, term: &TermC, typ: &Type) -> Result<()> {
    unimplemented!()
    /*
    match (term.kind(), typ.kind()) {
        (TermCKind::Inf(e), _) => {
            let tp = &typeI(i,c,e)?;
            if typ != tp {
                return Err(format!("[inf] type mismatch {:?}", (typ,tp)))
            }
            Ok(())
        }
        (TermCKind::Lam(e), TypeKind::Fun(t,tp)) => {
            let c = c.clone();
            c.push((Name::Local(i), Info::HasType(t.clone())));
            let s = substC(0,
        }
    }
        */
}
