type Int = i32;
use std::rc::Rc;

pub fn test() -> i32 {
    42
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct TermI(Box<TermIKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum TermIKind {
    Ann(TermC, Type),
    Bound(Int),
    Free(Name),
    App(TermI, TermC),
}


#[derive(Clone, Eq, PartialEq, Debug)]
struct TermC(Box<TermCKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum TermCKind {
    Inf(TermI),
    Lam(TermC)
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct Name(Box<NameKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum NameKind {
    Global(String),
    Local(Int),
    Quote(Int),
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct Type(Box<TypeKind>);

#[derive(Clone, Eq, PartialEq, Debug)]
enum TypeKind {
    TFree(Name),
    Fun(Type, Type),
}


#[derive(Clone)]
struct Value(Box<ValueKind>);

#[derive(Clone)]
enum ValueKind {
    VLam(Rc<dyn Fn(Value) -> Value>),
    Fun(Type, Type),
}


#[derive(Clone)]
struct Neutral(Box<NeutralKind>);

#[derive(Clone)]
enum NeutralKind {
    Free(Name),
    App(Neutral, Value),
}
