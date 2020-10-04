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

class Local(Name):
    __slots__ = ['i']
    def __init__(self, pos : int):
        self.i = pos
    def __repr__(self) -> str:
        return f"(Local {self.i})"

class Quote(Name):
    __slots__ = ['pos']
    def __init__(self, pos : int):
        self.pos = pos
    def __repr__(self) -> str:
        return f"(Quote {self.pos})"

@abstract
class Type: __slots__ = ['_']

class TFree(Type):
    __slots__ = ['x']
    def __init__(self, name : Name):
        self.x = name
    def __repr__(self) -> str:
        return f"(TFree {self.x})"

class Fun(Type):
    __slots__ = ['k','kp']
    def __init__(self, typePrm : Type, typeRes : Type):
        self.t = typePrm
        self.tp = typeRes
    def __repr__(self) -> str:
        return f"{self.t} -> {self.tp}"

@abstract
class Value: pass

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
class Neutral: pass

class NFree(Neutral):
    __slots__ = ['name']
    def __init__(self, name : Name):
        self.x = name
    def __repr__(self) -> str:
        return f"(NFree self.x)"
class NApp(Neutral):
    __slots__ = ['n', 'v']
    def __init__(self, neutral : Neutral, value : Value):
        self.n = neutral
        self.v = neutral
    def __repr__(self) -> str:
        return f"(NApp self.n self.v)"

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
class Kind: pass
class Star(Kind):
    __slots__ = ['_']
    def __repr__(self) -> str:
        return f"Star"

@abstract
class Info: pass
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
    raise TypeError(f"Unknown instance '{type(term)}'")

def typeI(i : int, c : Context, term : TermI) -> Type:
    if isinstance(term, Ann):
        kindC(c, term.t, Star())
        typeC(i, c, term.e, term.t)
        return term.t
    elif isinstance(term, TFree):
        info = c[term.x]
        if isinstance(info, HasType):
            return info.t
        else:
            raise RuntimeError(f"unknown type identifier '{term.x}'")
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
    raise TypeError(f"Type misamtch: term={term}', type={type}")

