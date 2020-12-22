type Int = i32;
use std::rc::Rc;

pub fn test() -> i32 {
    42
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct TermI(Rc<TermIKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum TermIKind {
    Ann(TermC, Type),
    Bound(Int),
    Free(Name),
    App(TermI, TermC),
}


#[derive(Clone, Eq, PartialEq, Debug)]
struct TermC(Rc<TermCKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum TermCKind {
    Inf(TermI),
    Lam(TermC)
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct Name(Rc<NameKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum NameKind {
    Global(String),
    Local(Int),
    Quote(Int),
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct Type(Rc<TypeKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum TypeKind {
    Free(Name),
    Fun(Type, Type),
}

#[derive(Clone)]
struct Value(Rc<ValueKind>);

#[derive(Clone)]
enum ValueKind {
    Lam(Rc<dyn Fn(Value) -> Value>),
    Neutral(Neutral),
}

impl Value {
    fn new(kind: ValueKind) -> Value {
        Value(Rc::new(kind))
    }
    fn Lam(v : Rc<dyn Fn(Value) -> Value>) -> Value {
        Value::new(ValueKind::Lam(v))
    }
    fn Neutral(n: Neutral) -> Value {
        Value::new(ValueKind::Neutral(n))
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
    fn new(kind: NeutralKind) -> Neutral {
        Neutral(Rc::new(kind))
    }

    fn Free(n: Name) -> Neutral {
        Neutral::new(NeutralKind::Free(n))
    }

    fn App(n: Neutral, v: Value) -> Neutral {
        Neutral::new(NeutralKind::App(n,v))
    }
}

fn free(n: &Name) -> Value {
    Value::Neutral(Neutral::Free(n.clone()))
}
