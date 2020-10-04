from __future__ import annotations

import typing as ty
from typing import Any as TAny, Callable as TLam, List as TList, \
                   Dict as TDict, Union as TUnion

AbstractF = ty.TypeVar('AbstractF', bound=TLam[..., TAny])
def abstract(cls : AbstractF) -> TAny:
    class Abstract(cls): # type: ignore
        __slots__ = cls.__slots__
        def __init__(self : Abstract, *args : TAny, **kwargs : TAny) -> None:
            if type(self) == Abstract:
                raise TypeError(f"'{cls.__name__}' is an abstract class")
            super().__init__(*args ,**kwargs)
    return Abstract

@abstract
class TermI:
    __slots__ = ['_']

class Ann(TermI):
    __slots__ = ['e1', 'e2']
    def __init__(self, e1 : TermC, e2 : TermC):
        super().__init__()
        self.e1 = e1
        self.e2 = e2
    def __repr__(self) -> str:
        return f"(Ann {self.e1}::{self.e2})"
    def __eq__(self, other : object) -> bool:
        assert(isinstance(other,Ann))
        return self.e1 == other.e1 and self.e2 == other.e2

class Star(TermI):
    __slots__ = ['_']
    def __repr__(self) -> str:
        return f"*"
    def __eq__(self, other : object) -> bool:
        assert(isinstance(other, Star))
        return True

class Pi(TermI):
    __slots__ = ['e1', 'e2']
    def __init__(self, e1 : TermC, e2 : TermC):
        super().__init__()
        self.e1 = e1
        self.e2 = e2
    def __repr__(self) -> str:
        return f"(Pi {self.e1}::{self.e2})"
    def __eq__(self, other : object) -> bool:
        assert(isinstance(other,Pi))
        return self.e1 == other.e1 and self.e2 == other.e2

class Bound(TermI):
    __slots__ = ['i']
    def __init__(self, pos : int):
        super().__init__()
        self.i = pos
    def __repr__(self) -> str:
        return f"(Bound {self.i})"
    def __eq__(self, other : object) -> bool:
        assert(isinstance(other,Bound))
        return self.i == other.i

class Free(TermI):
    __slots__ = ['x']
    def __init__(self, name : Name):
        self.x = name
    def __repr__(self) -> str:
        return f"{self.x}"
    def __eq__(self, other : object) -> bool:
        assert(isinstance(other,Free))
        return self.x == other.x

class App(TermI):
    __slots__ = ['e1','e2']
    def __init__(self, e1 : TermI, e2 : TermC):
        self.e1 = e1
        self.e2 = e2
    def __repr__(self) -> str:
        return f"(App {self.e1} {self.e2})"
    def __eq__(self, other : object) -> bool:
        assert(isinstance(other,App))
        return self.e1 == other.e1 and self.e2 == other.e2


@abstract
class TermC:
    __slots__ = ['_']
class Inf(TermC):
    __slots__ = ['e']
    def __init__(self, e : TermI):
        super().__init__()
        self.e = e
    def __repr__(self) -> str:
        return f"{self.e}"
    def __eq__(self, other : object) -> bool:
        assert(isinstance(other, Inf))
        return self.e == other.e

class Lam(TermC):
    __slots__ = ['e']
    def __init__(self, expr : TermC):
        self.e = expr
    def __repr__(self) -> str:
        return f"(Lam {self.e})"
    def __eq__(self, other :object) -> bool:
        assert(isinstance(other, Lam))
        return self.e == other.e

@abstract
class Name(): __slots__ = ['_']

class Global(Name):
    __slots__ = ['str']
    def __init__(self, str_ : str):
        self.str = str_
    def __repr__(self) -> str:
        return f"(Global {self.str})"
    def __eq__(self, other : object) -> bool:
        assert(isinstance(other, Global))
        return self.str == other.str
    def __hash__(self) -> TAny:
        return self.str.__hash__()

class Local(Name):
    __slots__ = ['i']
    def __init__(self, pos : int):
        self.i = pos
    def __repr__(self) -> str:
        return f"(Local {self.i})"
    def __eq__(self, other : object) -> bool:
        assert(isinstance(other, Local))
        return self.i == other.i
    def __hash__(self) -> TAny:
        return self.i.__hash__()

class Quote(Name):
    __slots__ = ['i']
    def __init__(self, pos : int):
        self.i = pos
    def __repr__(self) -> str:
        return f"(Quote {self.i})"
    def __eq__(self, other : object) -> bool:
        assert(isinstance(other, Quote))
        return self.i == other.i
    def __hash__(self) -> TAny:
        return self.i.__hash__()

@abstract
class Value:
    __slots__=['_']
    def __repr__(self) -> str:
        return f"{quote0(self)}"

class VLam(Value):
    __slots__ = ['f']
    def __init__(self, lam : TLam[[Value], Value]):
        self.f = lam
    def __eq__(self ,other :object) -> bool:
        assert False, "not comparable objects"

class VNeutral(Value):
    __slots__ = ['n']
    def __init__(self, neutral : Neutral):
        self.n = neutral
    def __eq__(self, other : object) -> bool:
        assert(isinstance(other, VNeutral))
        return self.n == other.n

class VStar(Value):
    __slots__ = ['n']
    def __eq__(self, other:object)->bool:
        assert(isinstance(other, VStar))
        return True

class VPi(Value):
    __slots__ = ['v', 'f']
    def __init__(self, v : Value, f : TLam[[Value], Value]):
        self.v = v
        self.f = f
    def __eq__(self ,other :object) -> bool:
        assert False, "not comparable objects"

@abstract
class Neutral: __slots__ = ['_']

class NFree(Neutral):
    __slots__ = ['x']
    def __init__(self, name : Name):
        self.x = name
    def __repr__(self) -> str:
        return f"(NFree {self.x})"
class NApp(Neutral):
    __slots__ = ['n', 'v']
    def __init__(self, neutral : Neutral, value : Value):
        self.n = neutral
        self.v = value
    def __repr__(self) -> str:
        return f"(NApp {self.n} {self.v})"

Type = Value
vfree : TLam[[Name],Value] = lambda n :  VNeutral(NFree(n))
Env = TList[Value]
Context = TDict[Name, Type]

def evalI(term : TermI, env : Env) -> Value:
    if isinstance(term, Ann):
        return evalC(term.e1, env)
    elif isinstance(term, Free):
        return vfree(term.x)
    elif isinstance(term, Bound):
        return env[term.i]
    elif isinstance(term, App):
        return vapp(evalI(term.e1, env), evalC(term.e2, env))
    elif isinstance(term, Star):
        return VStar()
    elif isinstance(term, Pi):
        e2 = term.e2
        return VPi(evalC(term.e1,env), lambda x: evalC(e2, [x] + env))
    raise TypeError(f"Unknown instance '{type(term)}'")

def vapp(v : Value, v1 : Value) -> Value:
    if isinstance(v, VLam):
        return v.f(v1)
    elif isinstance(v, VNeutral):
        return VNeutral(NApp(v.n, v1))
    raise TypeError(f"Unknown instance '{type(v)}'")

def evalC(term : TermC, env : Env) -> Value:
    if isinstance(term, Inf):
        return evalI(term.e, env)
    elif isinstance(term, Lam):
        lam_expr = term.e
        return VLam(lambda x : evalC(lam_expr, [x] + env))
    raise TypeError(f"Unknown instance '{type(term)}'")


def typeI0(c : Context, term : TermI) -> Type:
    return typeI(0, c, term)

def dict_merge(a : TDict[TAny, TAny],
               b : TDict[TAny, TAny]) -> TDict[TAny, TAny]:
    a = a.copy()
    a.update(b)
    return a

def typeI(i : int, c : Context, term : TermI) -> Type:
    if isinstance(term, Ann):
        typeC(i, c, term.e2, VStar())
        t = evalC(term.e2, [])
        typeC(i, c, term.e1, t)
        return t
    elif isinstance(term, Free):
        return c[term.x]
    elif isinstance(term, App):
        s = typeI(i, c, term.e1)
        if isinstance(s, VPi):
            typeC(i, c, term.e2, s.v)
            return s.f(evalC(term.e2, []))
    elif isinstance(term, Star):
        return VStar()
    elif isinstance(term, Pi):
        p = term.e1
        p1 = term.e2
        typeC(i,c,p,VStar())
        t = evalC(p, [])
        typeC(i+1,dict_merge({Local(i): t}, c),
                  substC(0, Free(Local(i)), p1),
                  VStar())
        return VStar()
    raise TypeError(f"Unknown instance '{type(term)}'")

def typeC(i : int, c: Context, term : TermC, ty : Type) -> None:
    e : TUnion[TermI, TermC]
    if isinstance(term, Inf):
        e = term.e
        v = ty
        v1 = typeI(i, c, e)
        if quote0(v) != quote0(v1):
            raise TypeError(f"type mismatch: {v} != {v1}")
        return
    elif isinstance(term, Lam) and isinstance(ty, VPi):
        e = term.e
        t = ty.v
        tp = ty.f
        typeC(i+1, dict_merge({Local(i): t}, c),
                   substC(0, Free(Local(i)), e), tp(vfree(Local(i))))
        return
    raise TypeError(f"Type mismatch: term={term}', type={type}")

def substI(i : int, r : TermI, t : TermI) -> TermI:
    if isinstance(t, Ann):
        return Ann(substC(i,r,t.e1), t.e2)
    elif isinstance(t, Bound):
        return r if i == t.i else t
    elif isinstance(t, Free):
        return t
    elif isinstance(t, App):
        return substI(i, r, App(t.e1, substC(i,r,t.e2)))
    elif isinstance(t, Star):
        return Star()
    elif isinstance(t, Pi):
        return Pi(substC(i,r,t.e1), substC(i+1, r, t.e2))
    raise TypeError(f"Unknown instance '{type(t)}'")

def substC(i : int, r : TermI, t : TermC) -> TermC:
    if isinstance(t, Inf):
        return Inf(substI(i,r,t.e))
    elif isinstance(t, Lam):
        return Lam(substC(i+1, r, t.e))
    raise TypeError(f"Unknown instance '{type(t)}'")

def quote0(v : Value) -> TermC:
    return quote(0,v)


def quote(i : int, v : Value) -> TermC:
    if isinstance(v, VLam):
        return Lam(quote(i+1, v.f(vfree(Quote(i)))))
    elif isinstance(v, VNeutral):
        return Inf(neutralQuote(i,v.n))
    elif isinstance(v, VStar):
        return Inf(Star())
    elif isinstance(v, VPi):
        return Inf(Pi(quote(i,v.v),
                      quote(i+1, v.f(vfree(Quote(i))))))
    raise TypeError(f"Unknown instance '{type(v)}'")

def neutralQuote(i : int, n : Neutral) -> TermI:
    if isinstance(n, NFree):
        return boundfree(i,n.x)
    elif isinstance(n, NApp):
        return App(neutralQuote(i, n.n), quote(i,n.v))
    raise TypeError(f"Unknown instance '{type(n)}'")

def boundfree(i : int, x : Name) -> TermI:
    if isinstance(x, Quote):
        return Bound(i-x.i-1)
    else:
        return Free(x)

###############################################################################
# Examples
###############################################################################

e0 = quote0 (VLam (lambda x : VLam (lambda y : x)))
print("e0=", e0)

id_ = Lam (Inf (Bound(0)))
const_ = Lam (Lam (Inf (Bound(1))))
free : TLam[[str],TermC] = lambda x : Inf (Free (Global(x)))
pi : TLam[[TermC, TermC], TermC] = lambda x,y : Inf(Pi(x,y))
term1 = App(Ann(id_,(pi (free("a"),free("a")))), free("y"))
term2 = App(App(Ann(const_,pi(pi(free("b"),free("b")),
                   pi(free("a"),
                        pi(free("b"),free("b"))))),
        id_), free("y"))
env1 : Context = {Global("y"): VNeutral(NFree(Global("a"))),
                  Global("a"): VStar()}
env2 = env1.copy()
env2.update({Global("b"): VStar()})

print("eval(term1)", evalI(term1, []))
print("qeval(term1)", quote0(evalI(term1, [])))
print("qqeval(term2)=", quote0(evalI(term2, [])))
print("type(term1)=", typeI0(env1, term1))
print("type(term2)=", typeI0(env2, term2))

# example for the following concrete syntax
# > let id = (\a x -> x) :: Pi (a :: *).a -> a
# id :: Pi (x::*) (y::x).x
e35 = Ann(
        Lam(
          Lam(Inf(Bound(0)))
        ),
        pi(
          (Inf(Star())),
          pi(
            Inf(Bound(0)),
            Inf(Bound(1)),
          )
        )
      )
print(f"e35= {e35}")

env35 : Context
env35 = {Global("Bool"):VStar(),
         Global("False"):VNeutral(NFree(Global("Bool")))}
print(f"type(e35)= {typeI0(env35, e35)}")

apply35a = App(e35, free("Bool"))
print(f"apply35a= {apply35a}")
print(f"type(apply35a)= {typeI0(env35, apply35a)}")

apply35b = App(apply35a, free("False"))
print(f"apply35b= {apply35b}")
print(f"type(apply35b)= {typeI0(env35, apply35b)}")
