type Int = i32;
use std::rc::Rc;

pub fn test() -> i32 {
    42
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TermI(Rc<TermIKind>);

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
pub struct TermC(Rc<TermCKind>);

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
pub struct Name(Rc<NameKind>);

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
pub struct Type(Rc<TypeKind>);

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
pub struct Value(Rc<ValueKind>);

#[derive(Clone)]
enum ValueKind {
    Lam(Rc<dyn Fn(&Value) -> Value>),
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
        Value(Rc::new(kind))
    }
    fn Lam(v: Rc<dyn Fn(&Value) -> Value>) -> Value {
        Value::new(ValueKind::Lam(v))
    }
    fn Neutral(n: Neutral) -> Value {
        Value::new(ValueKind::Neutral(n))
    }
    fn clone(&self) -> Value {
        Value(Rc::clone(&self.0))
    }
}

#[derive(Clone)]
struct Neutral(Rc<NeutralKind>);

#[derive(Clone)]
enum NeutralKind {
    Free(Name),
    App(Neutral, Value),
}

impl Neutral {
    #![allow(non_snake_case)]
    fn new(kind: NeutralKind) -> Neutral {
        Neutral(Rc::new(kind))
    }

    fn Free(n: Name) -> Neutral {
        Neutral::new(NeutralKind::Free(n))
    }

    fn App(n: Neutral, v: Value) -> Neutral {
        Neutral::new(NeutralKind::App(n, v))
    }
}

impl Neutral {
    fn kind(&self) -> &NeutralKind {
        return &*self.0;
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
            Value::Lam(Rc::new(move |x| {
                let mut env = env.clone();
                env.push_front(x.clone());
                evalC(&e, &env)
            }))
        }
    }
}

pub fn vapp(v1: &Value, v: &Value) -> Value {
    match v1.kind() {
        ValueKind::Lam(f) => f(v),
        ValueKind::Neutral(n) => Value::Neutral(Neutral::App(n.clone(), v.clone())),
    }
}
