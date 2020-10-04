from __future__ import annotations

import typing as ty
from typing import Any as TAny, Callable as TLam

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
    __slots__ = ['term', 'type']
    def __init__(self, term : TermC, type_ : Type):
        super().__init__()
        self.term = term
        self.type = type_
    def __repr__(self) -> str:
        return f"{self.term}::{self.type}"

class Bound(TermI):
    __slots__ = ['pos']
    def __init__(self, pos : int):
        super().__init__()
        self.pos = pos
    def __repr__(self) -> str:
        return f"(Bound {self.pos})"

class Free(TermI):
    __slots__ = ['name']
    def __init__(self, name : Name):
        self.name = name
    def __repr__(self) -> str:
        return f"(Free {self.name})"

class App(TermI):
    __slots__ = ['termFun','termArg']
    def __init__(self, termFun : TermI, termArg : TermC):
        self.termFun = termFun
        self.termArg = termArg
    def __repr__(self) -> str:
        return f"{self.termFun}@{self.termArg}"


@abstract
class TermC:
    __slots__ = ['_']
class Inf(TermC):
    __slots__ = ['term']
    def __init__(self, term : TermI):
        super().__init__()
        self.term = term
    def __repr__(self) -> str:
        return f"(Inf {self.term})"
class Lam(TermC):
    __slots__ = ['term']
    def __init__(self, term : TermC):
        self.term = term
    def __repr__(self) -> str:
        return f"(Lam {self.term})"

@abstract
class Name(): __slots__ = ['_']

class Global(Name):
    __slots__ = ['str']
    def __init__(self, str_ : str):
        self.str = str_
    def __repr__(self) -> str:
        return f"(Global {self.str})"

class Local(Name):
    __slots__ = ['pos']
    def __init__(self, pos : int):
        self.pos = pos
    def __repr__(self) -> str:
        return f"(Local {self.pos})"

class Quote(Name):
    __slots__ = ['pos']
    def __init__(self, pos : int):
        self.pos = pos
    def __repr__(self) -> str:
        return f"(Quote {self.pos})"

@abstract
class Type: __slots__ = ['_']

class TFree(Type):
    __slots__ = ['name']
    def __init__(self, name : Name):
        self.name = name
    def __repr__(self) -> str:
        return f"(TFree {self.name})"

class Fun(Type):
    __slots__ = ['typePrm','typeRes']
    def __init__(self, typePrm : Type, typeRes : Type):
        self.typePrm = typePrm
        self.typeRes = typeRes
    def __repr__(self) -> str:
        return f"{self.typePrm} -> {self.typeRes}"

@abstract
class Value: pass

class VLam(Value):
    __slots__ = ['lam']
    def __init__(self, lam : TLam[[Value], Value]):
        self.lam = lam
    def __repr__(self) -> str:
        return f"(VLam {self.lam})"

class VNeutral(Value):
    __slots__ = ['neutral']
    def __init__(self, neutral : Neutral):
        self.neutral = Neutral
    def __repr__(self) -> str:
        return f"(VNeutral {self.neutral})"

@abstract
class Neutral: pass

class NFree(Neutral):
    __slots__ = ['name']
    def __init__(self, name : Name):
        self.name = name
    def __repr__(self) -> str:
        return f"(NFree self.name)"
class NApp(Neutral):
    __slots__ = ['neutral', 'value']
    def __init__(self, neutral : Neutral, value : Value):
        self.neutral = neutral
        self.value = neutral
    def __repr__(self) -> str:
        return f"(NApp self.neutral self.value)"

