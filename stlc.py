from __future__ import annotations

import typing as ty
from typing import Any as TAny, Callable as TLam, List as TList, \
                   Dict as TDict

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
    __slots__ = ['e', 't']
    def __init__(self, expr : TermC, type_ : Type):
        super().__init__()
        self.e = expr
        self.t = type_
    def __repr__(self) -> str:
        return f"{self.e}::{self.t}"

class Bound(TermI):
    __slots__ = ['i']
    def __init__(self, pos : int):
        super().__init__()
        self.i = pos
    def __repr__(self) -> str:
        return f"(Bound {self.i})"

class Free(TermI):
    __slots__ = ['x']
    def __init__(self, name : Name):
        self.x = name
    def __repr__(self) -> str:
        return f"(Free {self.x})"

class App(TermI):
    __slots__ = ['e','ep']
    def __init__(self, termFun : TermI, termArg : TermC):
        self.e = termFun
        self.ep = termArg
    def __repr__(self) -> str:
        return f"{self.e}@{self.ep}"


@abstract
class TermC:
    __slots__ = ['_']
class Inf(TermC):
    __slots__ = ['i']
    def __init__(self, iterm : TermI):
        super().__init__()
        self.i = iterm
    def __repr__(self) -> str:
        return f"(Inf {self.i})"
class Lam(TermC):
    __slots__ = ['e']
    def __init__(self, expr : TermC):
        self.e = expr
    def __repr__(self) -> str:
        return f"(Lam {self.e})"

@abstract
class Name(): __slots__ = ['_']

class Global(Name):
    __slots__ = ['str']
    def __init__(self, str_ : str):
        self.str = str_
    def __repr__(self) -> str:
        return f"(Global {self.str})"
    def __eq__(self, other : Global) -> bool: # type: ignore
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
    def __eq__(self, other : Local) -> bool: # type: ignore
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
    def __eq__(self, other : Quote) -> bool: # type: ignore
        assert(isinstance(other, Quote))
        return self.i == other.i
    def __hash__(self) -> TAny:
        return self.i.__hash__()

@abstract
class Type: __slots__ = ['_']

class TFree(Type):
    __slots__ = ['x']
    def __init__(self, name : Name):
        self.x = name
    def __repr__(self) -> str:
        return f"(TFree {self.x})"
    def __eq__(self, other : TFree) -> bool: # type: ignore
        assert(isinstance(other, TFree))
        return self.x == other.x

class Fun(Type):
    __slots__ = ['t','tp']
    def __init__(self, typePrm : Type, typeRes : Type):
        self.t = typePrm
        self.tp = typeRes
    def __repr__(self) -> str:
        return f"(Fun {self.t} {self.tp})"
    def __eq__(self, other : Fun) -> bool: # type: ignore
        assert(isinstance(other, Fun))
        return self.t == other.tp and self.tp == other.tp

@abstract
class Value: __slots__=['_']

class VLam(Value):
    __slots__ = ['f']
    def __init__(self, lam : TLam[[Value], Value]):
        self.f = lam
    def __repr__(self) -> str:
        return f"(VLam {self.f})"

class VNeutral(Value):
    __slots__ = ['n']
    def __init__(self, neutral : Neutral):
        self.n = neutral
    def __repr__(self) -> str:
        return f"(VNeutral {self.n})"

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

vfree : TLam[[Name],Value] = lambda n :  VNeutral(NFree(n))

Env = TList[Value]

def evalI(term : TermI, env : Env) -> Value:
    if isinstance(term, Ann):
        return evalC(term.e, env)
    elif isinstance(term, Free):
        return vfree(term.x)
    elif isinstance(term, Bound):
        return env[term.i]
    elif isinstance(term, App):
        return vapp(evalI(term.e, env), evalC(term.ep, env))
    raise TypeError(f"Unknown instance '{type(term)}'")

def vapp(v : Value, v1 : Value) -> Value:
    if isinstance(v, VLam):
        return v.f(v1)
    elif isinstance(v, VNeutral):
        return VNeutral(NApp(v.n, v1))
    raise TypeError(f"Unknown instance '{type(v)}'")

def evalC(term : TermC, env : Env) -> Value:
    if isinstance(term, Inf):
        return evalI(term.i, env)
    elif isinstance(term, Lam):
        lam_expr = term.e
        return VLam(lambda x : evalC(lam_expr, [x] + env))
    raise TypeError(f"Unknown instance '{type(term)}'")

@abstract
class Kind: __slots__ = ['_']
class Star(Kind):
    __slots__ = ['_']
    def __repr__(self) -> str:
        return f"Star"

@abstract
class Info: __slots__ = ['_']
class HasKind(Info):
    __slots__ = ['kind']
    def __init__(self, kind : Kind):
        self.kind = kind
    def __repr__(self) -> str:
        return f"(HasKind {self.kind})"
class HasType(Info):
    __slots__ = ['t']
    def __init__(self, type_ : Type):
        self.t = type_
    def __repr__(self) -> str:
        return f"(HasType {self.t})"

Context = TDict[Name, Info]

def kindC(c : Context, term : Type, k : Kind) -> None:
    assert(isinstance(k, Star))
    if isinstance(term, TFree):
        if isinstance(c[term.x], HasKind):
            return
        else:
            raise RuntimeError(f"unknown var identifier '{term.x}'")
    elif isinstance(term, Fun):
        kindC(c, term.t, Star())
        kindC(c, term.tp, Star())
        return
    raise TypeError(f"Unknown instance '{type(term)}'")

def typeI0(c : Context, term : TermI) -> Type:
    return typeI(0, c, term)

def typeI(i : int, c : Context, term : TermI) -> Type:
    if isinstance(term, Ann):
        kindC(c, term.t, Star())
        typeC(i, c, term.e, term.t)
        return term.t
    elif isinstance(term, Free):
        info = c[term.x]
        if isinstance(info, HasType):
            return info.t
        else:
            raise RuntimeError(f"unknown type identifier '{term.x}'")
    elif isinstance(term, App):
        f = typeI(i, c, term.e)
        if isinstance(f, Fun):
            typeC(i, c, term.ep, f.t)
            return f.tp
    raise TypeError(f"Unknown instance '{type(term)}'")

def dict_merge(a : TDict[TAny, TAny],
               b : TDict[TAny, TAny]) -> TDict[TAny, TAny]:
    a = a.copy()
    a.update(b)
    return a

def typeC(i : int, c: Context, term : TermC, ty : Type) -> None:
    if isinstance(term, Inf):
        ty1 = typeI(i, c, term.i)
        if ty != ty1:
            raise TypeError(f"type mismatch: {ty} != {ty1}")
        return
    elif isinstance(term, Lam) and isinstance(ty, Fun):
        typeC(i+1, dict_merge({Local(i): HasType(ty.t)}, c),
                   substC(0, Free(Local(i)), term.e), ty.tp)
        return
    raise TypeError(f"Type mismatch: term={term}', type={type}")

def substI(i : int, r : TermI, t : TermI) -> TermI:
    if isinstance(t, Ann):
        return Ann(substC(i,r,t.e), t.t)
    elif isinstance(t, Bound):
        return r if i == t.i else t
    elif isinstance(t, Free):
        return t
    elif isinstance(t, App):
        return substI(i, r, App(t.e, substC(i,r,t.ep)))
    raise TypeError(f"Unknown instance '{type(t)}'")

def substC(i : int, r : TermI, t : TermC) -> TermC:
    if isinstance(t, Inf):
        return Inf(substI(i,r,t.i))
    elif isinstance(t, Lam):
        return Lam(substC(i+1, r, t.e))
    raise TypeError(f"Unknown instance '{type(t)}'")

def quote0(v : Value) -> TermC:
    return quote(0,v)


"""
--------------------------------------------------
@claim
def quote1(_1 : int, _2 : Value) -> TermC: pass

generates:
quote1__dict = dict()
def quote1(_1 : int, _2 : Value) -> TermC:
    assert(isinstance(_1,int))
    assert(isinstance(_2,Value))
    quote1__args = (int, Value)
    return quote1_dict["_1__{int.__name__},
                        _2__{Value.__name__}"](_1, _2)

-----------------------------------------------------

@define
def quote1(i, _1 : VLam(f)):
    return Lam(quote(i+1, f(vfree(Quote(i)))))

generates

quote1__dict.update(f"_1__{int.__name__},
                      _2__{VLam.__name__}":quote1__VLam)
def quote1__VLam(_1 : int, _2 : VLam) -> TermC:
    assert(isinstance(_2, VLam))
    i = _1
    f = _2.expr
    return Lam(quote(i+1, f(vfree(Quote(i)))))

-------------------------------------------

@match
def quote1(i, _ : VNeutral(n)):
    return Inf(neutralQuote(i,n))

generates

quote1__dict.update(f"_1__{int.__name__},
                      _2__{NVeutral.__name__}":quote1__VNeutral)

def quote1__VNeutral(_1 : int, _2 : VNeutral) -> TermC:
    assert(isinstancE(_2, VNeutral))
    i = _1
    n = _2.neutral
    return Inf(Neutral(i,n))
"""

def quote(i : int, v : Value) -> TermC:
    if isinstance(v, VLam):
        return Lam(quote(i+1, v.f(vfree(Quote(i)))))
    elif isinstance(v, VNeutral):
        return Inf(neutralQuote(i,v.n))
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

#e0 = quote0 (VLam (lambda x : VLam (lambda y : x)))
#print(e0)

id_ = Lam (Inf (Bound(0)))
const_ = Lam (Lam (Inf (Bound(1))))
tfree : TLam[[str], TFree] = lambda a : TFree (Global(a))
free : TLam[[str],Inf] = lambda x : Inf (Free (Global(x)))
term1 = App(Ann(id_,(Fun (tfree("a"),tfree("a")))), free("y"))
term2 = App(App(Ann(const_,Fun (Fun(tfree("b"),tfree("b")),
                   (Fun (tfree("a"),
                        (Fun (tfree("b"),tfree("b"))))))),
        id_), free("y"))
env1 : Context = {Global("y"): HasType(tfree("a")),
                  Global("a"): HasKind(Star())}
env2 = env1.copy()
env2.update({Global("b"): HasKind(Star())})

print(evalI(term1, []))
print(quote0(evalI(term1, [])))
print(quote0(evalI(term2, [])))
print(typeI0(env1, term1))
print(typeI0(env2, term2))
