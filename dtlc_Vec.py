# run 'mypy' on this source tree, e.g. form the root repo folder, run
# ```
# $ mypy
# Success: no issues found in 4 source files
# ```
# see mypy.ini for configuration for mypy.
#

from __future__ import annotations

from typing import (
    Any as TAny,
    Callable as TLam,
    List as TList,
    Dict as TDict,
    Union as TUnion,
    Type as TType,
    TypeVar as TTypeVar,
    Generic as TGeneric,
    Tuple as TTuple,
    cast as _cast,
    Iterator as TIter,
)
import sys
from dataclasses import dataclass
import dataclasses as _dc
import typeguard
import functools
from functools import reduce as fold

foldl: TLam[[TAny, TAny, TAny], TAny] = lambda func, acc, xs: functools.reduce(
    func, xs, acc
)

_dc_attrs = {"frozen": True, "repr": False}


_match_contextT = TTypeVar("_match_contextT")
class _match_context(TGeneric[_match_contextT]):
    class _skip(Exception):
        pass

    def __init__(self, obj: TAny, cls: TAny):
        self.skip = not isinstance(obj, cls)
        self.obj = obj

    def __enter__(self) -> _match_contextT:
        if self.skip:
            import sys

            sys.settrace(lambda *args, **keys: None)
            frame = sys._getframe(1)
            frame.f_trace = self.trace  # type: ignore
            return None # type: ignore
        return self.obj

    def trace(self, frame, event, arg):  # type: ignore
        raise _match_context._skip()

    def __exit__(self, type, value, traceback):  # type: ignore
        if type is None:
            return  # No exception
        if issubclass(type, _match_context._skip):
            return True  # Suppress special SkipWithBlock exception


class Unpack:
    _T = TTypeVar("_T")
    def __iter__(self) -> TIter[TAny]:
        yield from [getattr(self, field.name) for field in _dc.fields(self)]

    def __repr__(self) -> str:
        string = f"{self.__class__.__name__}("
        keys = [field.name for field in _dc.fields(self)]
        for i, k in enumerate(keys):
            value = getattr(self, k)
            if isinstance(value, str):
                string += f"'{value}'"
            else:
                string += f"{value}"
            if i < len(keys) - 1:
                string += ","
        string += ")"
        return string

    def __ror__(self, cls: TType[_T]) -> _match_context[_T]:
        return _match_context(self, cls)


check_types = True
# check_types = False
check_argument_types: TLam[[], bool]
if check_types:
    check_argument_types = typeguard.check_argument_types
else:
    check_argument_types = lambda: True

# --WAR-beg--  mypy issue: https://github.com/python/mypy/issues/5485
_BoxT = TTypeVar("_BoxT")


@dataclass
class Box(TGeneric[_BoxT]):
    inner: _BoxT  # pytype: disable=not-supported-yet

    @property
    def __call__(self) -> _BoxT:
        return self.inner


# --WAR-end--


abstract = dataclass(frozen=True)


# mypy WAR for current lack of python forward declration, use strings :)
TermI = TUnion[
    "Ann",
    "Star",
    "Pi",
    "Bound",
    "Free",
    "App",
    "Nat",
    "NatElim",
    "Zero",
    "Succ",
    "Vec",
    "Nil",
    "Cons",
    "VecElim",
]


@dataclass(**_dc_attrs)
class Ann(Unpack):
    e1: TermC
    e2: TermC

@dataclass(**_dc_attrs)
class Star(Unpack):
    def __repr__(self) -> str:
        return f"*"


@dataclass(**_dc_attrs)
class Pi(Unpack):
    e1: TermC
    e2: TermC


@dataclass(**_dc_attrs)
class Bound(Unpack):
    i: int

    def __repr__(self) -> str:
        return f"(Bound {self.i})"


@dataclass(**_dc_attrs)
class Free(Unpack):
    x: Name

    def __repr__(self) -> str:
        return f"{self.x}"


@dataclass(**_dc_attrs)
class App(Unpack):
    e1: TermI
    e2: TermC


@dataclass(**_dc_attrs)
class Nat(Unpack):
    def __repr__(self) -> str:
        return "Nat"


@dataclass(**_dc_attrs)
class NatElim(Unpack):
    e1: TermC
    e2: TermC
    e3: TermC
    e4: TermC


@dataclass(**_dc_attrs)
class Zero(Unpack):
    def __repr__(self) -> str:
        return "Zero"


@dataclass(**_dc_attrs)
class Succ(Unpack):
    k: TermC

    def __repr__(self) -> str:
        return f"(Succ {self.k})"


@dataclass(**_dc_attrs)
class Vec(Unpack):
    a: TermC
    n: TermC

    def __repr__(self) -> str:
        return f"(Vec {self.a} {self.n})"


@dataclass(**_dc_attrs)
class Nil(Unpack):
    a: TermC

    def __repr__(self) -> str:
        return f"(Nil {self.a})"


@dataclass(**_dc_attrs)
class Cons(Unpack):
    a: TermC
    n: TermC
    x: TermC
    xs: TermC

    def __repr__(self) -> str:
        return f"(Cons {self.a} {self.n} {self.x} {self.xs})"


@dataclass(**_dc_attrs)
class VecElim(Unpack):
    a: TermC
    m: TermC
    mn: TermC
    mc: TermC
    n: TermC
    xs: TermC


TermC = TUnion["Inf", "Lam"]


@dataclass(**_dc_attrs)
class Inf(Unpack):
    e: TermI

    def __repr__(self) -> str:
        return f"{self.e}"


@dataclass(**_dc_attrs)
class Lam(Unpack):
    e: TermC


Name = TUnion["Global", "Local", "Quote"]


@dataclass(**_dc_attrs)
class Global(Unpack):
    str_: str

    def __repr__(self) -> str:
        return f"'{self.str_}'"


@dataclass(**_dc_attrs)
class Local(Unpack):
    i: int


@dataclass(**_dc_attrs)
class Quote(Unpack):
    i: int


_VFunT0 = TLam[["Value"], "Value"]
_VFunT = TUnion[Box[_VFunT0], _VFunT0]


@dataclass(**_dc_attrs)
class VLam(Unpack):
    f: _VFunT

    def __repr__(self) -> str:
        return f"{quote0(self)}"


@dataclass(**_dc_attrs)
class VNeutral(Unpack):
    n: Neutral


@dataclass(**_dc_attrs)
class VStar(Unpack):
    def __repr__(self) -> str:
        return f"*"


@dataclass(**_dc_attrs)
class VPi(Unpack):
    v: Value
    f: _VFunT

    def __repr__(self) -> str:
        return f"{quote0(self)}"


@dataclass(**_dc_attrs)
class VNat(Unpack):
    pass


@dataclass(**_dc_attrs)
class VZero(Unpack):
    pass


@dataclass(**_dc_attrs)
class VSucc(Unpack):
    k: Value

    def __repr__(self) -> str:
        return f"{quote0(self)}"


@dataclass(**_dc_attrs)
class VNil(Unpack):
    a: Value

    def __repr__(self) -> str:
        return f"{quote0(self)}"


@dataclass(**_dc_attrs)
class VCons(Unpack):
    a: Value
    n: Value
    x: Value
    xs: Value

    def __repr__(self) -> str:
        return f"{quote0(self)}"


@dataclass(**_dc_attrs)
class VVec(Unpack):
    a: Value
    n: Value

    def __repr__(self) -> str:
        return f"{quote0(self)}"


Value = TUnion[VLam, VNeutral, VStar, VPi, VNat, VZero, VSucc, VNil, VCons, VVec]


Neutral = TUnion["NFree", "NApp", "NNatElim", "NVecElim"]


@dataclass(**_dc_attrs)
class NFree(Unpack):
    x: Name


@dataclass(**_dc_attrs)
class NApp(Unpack):
    n: Neutral
    v: Value


@dataclass(**_dc_attrs)
class NNatElim(Unpack):
    a: Value
    n: Value
    x: Value
    xs: Neutral


@dataclass(**_dc_attrs)
class NVecElim(Unpack):
    v1: Value
    v2: Value
    v3: Value
    v4: Value
    v5: Value
    n: Neutral


Type = Value
vfree: TLam[[Name], Value] = lambda n: VNeutral(NFree(n))
Env = TList[Value]
Context = TDict[Name, Type]


def evalI(term: TermI, env: Env) -> Value:
    with Ann|term as (e, _):
        return evalC(e, env)
    with Free|term as (x,):
        return vfree(x)
    with Bound|term as (i,):
        return env[i]
    with App|term as (e, e1):
        return vapp(evalI(e, env), evalC(e1, env))
    with Star|term:
        return VStar()
    with Pi|term as (t, t1):
        return VPi(evalC(t, env), lambda x: evalC(t1, [x] + env))
    with Nat|term:
        return VNat()
    with Zero|term:
        return VZero()
    with Succ|term as (k,):
        return VSucc(evalC(k, env))
    with NatElim|term as (m, mz, ms, k):
        mzVal = evalC(mz, env)
        msVal = evalC(ms, env)

        def rec1(kVal: Value) -> Value:
            with VZero|kVal:
                return mzVal
            with VSucc|kVal as (k,):
                return vapp(vapp(msVal, k), rec1(k))
            with VNeutral|kVal as (n,):
                return VNeutral(NNatElim(evalC(m, env), mzVal, msVal, n))
            raise TypeError(f"Unknown instance '{type(kVal)}'")

        return rec1(evalC(k, env))
    with Vec|term as (a, n):
        return VVec(evalC(a, env), evalC(n, env))
    with Nil|term as (a,):
        return VNil(evalC(a, env))
    with Cons|term as (a,n,x,xs):
        return VCons(evalC(a, env), evalC(n, env), evalC(x, env), evalC(xs, env))
    with VecElim|term as (a,m,mn,mc,n,xs):
        mnVal = evalC(mn, env)
        mcVal = evalC(mc, env)

        def rec2(nVal: Value, xsVal: Value) -> Value:
            with VNil|xsVal:
                return mnVal
            with VCons|xsVal as (_, l, x, xs):
                return fold(vapp, [l, x, xs, rec2(l, xs)], mcVal)
            with VNeutral|xsVal as (n,):
                return VNeutral(
                    NVecElim(evalC(a, env), evalC(m, env), mnVal, mcVal, nVal, n)
                )
            raise TypeError(f"Unknown instance '{type(xsVal)}'")

        return rec2(evalC(n, env), evalC(xs, env))
    raise TypeError(f"Unknown instance '{type(term)}'")


def vapp(value: Value, v: Value) -> Value:
    with VLam|value as (f,):
        return f(v)
    with VNeutral|value as (n,):
        return VNeutral(NApp(n, v))
    raise TypeError(f"Unknown instance '{type(v)}'")


def evalC(term: TermC, env: Env) -> Value:
    with Inf|term as (e,):
        return evalI(e, env)
    with Lam|term as (lam_expr,):
        return VLam(lambda x: evalC(lam_expr, [x] + env))
    raise TypeError(f"Unknown instance '{type(term)}'")


def typeI0(c: Context, term: TermI) -> Type:
    check_argument_types()
    return typeI(0, c, term)


def dict_merge(a: TDict[TAny, TAny], b: TDict[TAny, TAny]) -> TDict[TAny, TAny]:
    a = a.copy()
    a.update(b)
    return a


def typeI(i: int, c: Context, term: TermI) -> Type:
#    with Ann|term as p:
#        reveal_type(p)
    with Ann|term as (e1,e2):
        typeC(i, c, e2, VStar())
        t = evalC(e2, [])
        typeC(i, c, e1, t)
        return t
    with Free|term as (x,):
        return c[x]
    with App|term as (e1,e2):
        s = typeI(i, c, e1)
        with VPi|s as (v,f):
            typeC(i, c, e2, v)
            return f(evalC(e2, []))
        raise TypeError(f"Illegal application: {e1}({e2})")
    with Star|term:
        return VStar()
    with Pi|term as (p,p1):
        typeC(i, c, p, VStar())
        t = evalC(p, [])
        typeC(
            i + 1, dict_merge({Local(i): t}, c), substC(0, Free(Local(i)), p1), VStar()
        )
        return VStar()
    with Nat|term:
        return VStar()
    with Zero|term:
        return VNat()
    with Succ|term:
        return VNat()
    with NatElim|term as (m,mz,ms,k):
        typeC(i, c, m, VPi(VNat(), lambda _: VStar()))
        mVal = evalC(m, [])
        typeC(i, c, mz, vapp(mVal, VZero()))
        typeC(
            i,
            c,
            ms,
            VPi(VNat(), lambda l: VPi(vapp(mVal, l), lambda _: vapp(mVal, VSucc(l)))),
        )
        typeC(i, c, k, VNat())
        kVal = evalC(k, [])
        return vapp(mVal, kVal)
    with Vec|term as (a,n):
        typeC(i, c, a, VStar())
        typeC(i, c, n, VNat())
        return VStar()
    with Nil|term as (a,):
        typeC(i, c, a, VStar())
        aVal = evalC(a, [])
        return VVec(aVal, VZero())
    with Cons|term as (a,k,x,xs):
        typeC(i, c, a, VStar())
        aVal = evalC(a, [])
        typeC(i, c, k, VNat())
        kVal = evalC(k, [])
        typeC(i, c, x, aVal)
        typeC(i, c, xs, VVec(aVal, kVal))
        return VVec(aVal, VSucc(kVal))
    with VecElim|term as (a,m,mn,mc,k,vs):
        typeC(i, c, a, VStar())
        aVal = evalC(a, [])
        typeC(i, c, m, VPi(VNat(), lambda k: VPi(VVec(aVal, k), lambda _: VStar())))
        mVal = evalC(m, [])
        typeC(i, c, mn, foldl(vapp, mVal, [VZero(), VNil(aVal)]))
        typeC(
            i,
            c,
            mc,
            VPi(
                VNat(),
                lambda l: VPi(
                    aVal,
                    lambda y: VPi(
                        VVec(aVal, l),
                        lambda ys: VPi(
                            foldl(vapp, mVal, [l, ys]),
                            lambda _: foldl(
                                vapp, mVal, [VSucc(l), VCons(aVal, l, y, ys)]
                            ),
                        ),
                    ),
                ),
            ),
        )
        typeC(i, c, k, VNat())
        kVal = evalC(k, [])
        typeC(i, c, vs, VVec(aVal, kVal))
        vsVal = evalC(vs, [])
        return fold(vapp, [kVal, vsVal], mVal)
    raise TypeError(f"Unknown instance '{type(term)}'")


def typeC(i: int, c: Context, term: TermC, type_: Type) -> None:
    with Inf|term as (e,):
        v = type_
        vp = typeI(i, c, e)
        if quote0(v) != quote0(vp):
            raise TypeError(f"type mismatch: {quote0(v)} != {quote0(vp)}")
        return
    with Lam|term as (e,), VPi|type_ as (t,tp):
        typeC(
            i + 1,
            dict_merge({Local(i): t}, c),
            substC(0, Free(Local(i)), e),
            tp(vfree(Local(i))),
        )
        return
    raise TypeError(f"Type mismatch: term={type(term)}', type={type(type_)}")


def substI(i: int, r: TermI, t: TermI) -> TermI:
    with Ann|t as (e1,e2):
        e1, e2 = t
        return Ann(substC(i, r, e1), e2)
    with Bound|t as (j,):
        return r if i == j else Bound(j)
    with Free|t:
        return t
    with App|t as (e1,e2):
        return App(substI(i, r, e1), substC(i, r, e2))
    with Star|t:
        return Star()
    with Pi|t as (f,v):
        return Pi(substC(i, r, f), substC(i + 1, r, v))
    with Nat|t:
        return Nat()
    with Zero|t:
        return Zero()
    with Succ|t as (k,):
        return Succ(substC(i, r, k))
    with NatElim|t as (m,mz,ms,k):
        return NatElim(
            substC(i, r, m), substC(i, r, mz), substC(i, r, ms), substC(i, r, k)
        )
    with Vec|t as (a,n):
        return Vec(substC(i, r, a), substC(i, r, n))
    with Nil|t as (a,):
        return Nil(substC(i, r, a))
    with Cons|t as (a,n,x,xs):
        return Cons(substC(i, r, a), substC(i, r, n), substC(i, r, x), substC(i, r, xs))
    with VecElim|t as (a,m,mn,mc,n,xs):
        return VecElim(
            substC(i, r, a),
            substC(i, r, m),
            substC(i, r, mn),
            substC(i, r, mc),
            substC(i, r, n),
            substC(i, r, xs),
        )
    raise TypeError(f"Unknown instance '{type(t)}'")


def substC(i: int, r: TermI, t: TermC) -> TermC:
    with Inf|t as (e,):
        return Inf(substI(i, r, e))
    with Lam|t as (e,):
        return Lam(substC(i + 1, r, e))
    raise TypeError(f"Unknown instance '{type(t)}'")


def quote0(v: Value) -> TermC:
    check_argument_types()
    return quote(0, v)


def quote(i: int, value: Value) -> TermC:
    with VLam|value as (f,):
        return Lam(quote(i + 1, f(vfree(Quote(i)))))
    with VNeutral|value as (n,):
        return Inf(neutralQuote(i, n))
    with VStar|value:
        return Inf(Star())
    with VPi|value as (v,f):
        return Inf(Pi(quote(i, v), quote(i + 1, f(vfree(Quote(i))))))
    with VNat|value:
        return Inf(Nat())
    with VZero|value:
        return Inf(Zero())
    with VSucc|value as (k,):
        return Inf(Succ(quote(i, k)))
    with VNil|value as (a,):
        return Inf(Nil(quote(i, a)))
    with VVec|value as (a,n):
        return Inf(Vec(quote(i, a), quote(i, n)))
    with VCons|value as (a,n,x,xs):
        return Inf(Cons(quote(i, a), quote(i, n), quote(i, x), quote(i, xs)))
    raise TypeError(f"Unknown instance '{type(value)}'")


def neutralQuote(i: int, neutral: Neutral) -> TermI:
    with NFree|neutral as (x,):
        return boundfree(i, x)
    with NApp|neutral as (n,v):
        return App(neutralQuote(i, n), quote(i, v))
    with NNatElim|neutral as (a,n,x,xs):
        return NatElim(
            quote(i, a), quote(i, n), quote(i, x), Inf(neutralQuote(i, xs))
        )
    raise TypeError(f"Unknown instance '{type(neutral)}'")


def boundfree(i: int, x: Name) -> TermI:
    check_argument_types()
    with Quote|x as (i,):
        return Bound(i - i - 1)
    return Free(x)


###############################################################################
# Examples
###############################################################################

e0 = quote0(VLam(lambda x: VLam(lambda y: x)))
print("e0=", e0)

id_ = Lam(Inf(Bound(0)))
const_ = Lam(Lam(Inf(Bound(1))))
free: TLam[[str], TermC] = lambda x: Inf(Free(Global(x)))
pi: TLam[[TermC, TermC], TermC] = lambda x, y: Inf(Pi(x, y))
term1 = App(Ann(id_, (pi(free("a"), free("a")))), free("y"))
term2 = App(
    App(
        Ann(
            const_,
            pi(pi(free("b"), free("b")), pi(free("a"), pi(free("b"), free("b")))),
        ),
        id_,
    ),
    free("y"),
)
env1: Context = {Global("y"): VNeutral(NFree(Global("a"))), Global("a"): VStar()}
env2 = env1.copy()
env2.update({Global("b"): VStar()})

print("eval(term1)=", evalI(term1, []))
print("qeval(term1)=", quote0(evalI(term1, [])))
print("qqeval(term2)=", quote0(evalI(term2, [])))
print("type(term1)=", typeI0(env1, term1))
print("type(term2)=", typeI0(env2, term2))

# example for the following concrete syntax
# > let id = (\a x -> x) :: Pi (a :: *).a -> a
# id :: Pi (x::*) (y::x).x
e35 = Ann(
    Lam(Lam(Inf(Bound(0)))),
    pi(
        (Inf(Star())),
        pi(
            Inf(Bound(0)),
            Inf(Bound(1)),
        ),
    ),
)
print(f"e35= {e35}")

env35: Context
env35 = {Global("Bool"): VStar(), Global("False"): VNeutral(NFree(Global("Bool")))}
print(f"type(e35)= {typeI0(env35, e35)}")

apply35a = App(e35, free("Bool"))
print(f"apply35a= {apply35a}")
print(f"type(apply35a)= {typeI0(env35, apply35a)}")

apply35b = App(apply35a, free("False"))
print(f"apply35b= {apply35b}")
print(f"type(apply35b)= {typeI0(env35, apply35b)}")

## > let plus = natElim (\_ -> Nat -> Nat)
##                      (\n -> n)
##                      (\k rec n -> Succ (rec n))
## plus :: Pi (x :: Nat) (y :: Nat) . Nat

plusl: TLam[[TermC], TermI] = lambda x: NatElim(
    Lam(pi(Inf(Nat()), Inf(Nat()))),
    Lam(Inf(Bound(0))),
    Lam(Lam(Lam(Inf(Succ(Inf(App(Bound(1), Inf(Bound(0))))))))),
    x,
)

Plus = Ann(
    Lam(
        Inf(
            NatElim(
                Lam(pi(Inf(Nat()), Inf(Nat()))),
                Lam(Inf(Bound(0))),
                Lam(Lam(Lam(Inf(Succ(Inf(App(Bound(1), Inf(Bound(0))))))))),
                Inf(Bound(0)),
            )
        )
    ),
    pi(Inf(Nat()), pi(Inf(Nat()), Inf(Nat()))),
)
print("type(Plus)=", typeI0({}, Plus))


def int2nat(n: int) -> TermC:
    if n == 0:
        return Inf(Zero())
    else:
        return Inf(Succ(int2nat(n - 1)))


def nval2int(v: Value) -> int:
    with VZero|v:
        return 0
    with VSucc|v as (k,):
        return 1 + nval2int(k)
    raise TypeError(f"Unknown instance '{type(v)}'")


print("2+2 ->", nval2int(evalI(App(App(Plus, int2nat(2)), int2nat(2)), [])))
# sys.exit(0)

## > plus 40 2
## 42 :: Nat
n40 = int2nat(40)
print("n40=", n40)
n2 = int2nat(2)
print("n2=", n2)
print("type(n40)=", typeI0({}, _cast(Inf, n40).e))
print("type(plusl(n40))=", typeI0({}, plusl(n40)))
n42term = App(plusl(n40), n2)
print("type(n42term)=", typeI0({}, n42term))
n42v = evalI(n42term, [])
print("n42v=", n42v)
n42 = nval2int(n42v)
print("n42=", n42)
## > n42
## 42

from functools import partial

"""
class Infix1(object):
    T = TTypeVar("T")
    U = TTypeVar("U")
    R = TTypeVar("R")
    def __init__(self, func : TUnion[TLam[[U],R], TLam[[T,U],R]]):
        self.func = func
    def __or__(self, other : U) -> R:
        return _cast(TLam[[Infix.U],Infix.R],self.func)(other)
    def __ror__(self, other : T) -> Infix:
        return Infix(partial(self.func, other)) #type: ignore

@Infix
def app1(x : TermI, y : TermC) -> TermI:
    return App(x,y)
"""


class Infix(object):
    def __init__(self, func: TUnion[TLam[[TAny], TAny], TLam[[TAny, TAny], TAny]]):
        self.func = func

    def __or__(self, other: TAny) -> TAny:
        return _cast(TLam[[TAny], TAny], self.func)(other)

    def __ror__(self, other: TAny) -> Infix:
        return Infix(partial(self.func, other))


@Infix
def app(x: TermI, y: TermC) -> TermI:
    return App(x, y)


n1 = int2nat(1)
n2a = plusl(n1) | app | n1
print("n2a=", n2a)
print("type(n2a)=", typeI0({}, n2a))
n2e = evalI(n2a, [])
print("n2e=", n2e)
print("n2e=", nval2int(n2e))
n4 = App(plusl(Inf(n2a)), Inf(n2a))
print("n4=", n4, type(n4).__class__)
print("type(n4)=", typeI0({}, n4))
print("eval(n4)=", nval2int(evalI(n4, [])))

## example from 4.2
## ##################
## > let append =
## >   (\a -> vecElim a
##                    (\m _ -> Pi (n :: Nat) . Vec a n -> Vec a (plus m n))
##                    (\_ v -> v)
##                    (\m v vs rec n w -> Cons a (plus m n) v (rec n w)))
## append :: Pi (a :: *) (m :: Nat) (v :: Vec a m) (n :: Nat) (w :: Vec a n) .
##           Vec a (plus m n)

## > assume (a :: *) (x :: a) (y :: a)
## > append a 2 (Cons a 1 x (Cons a 0 x (Nil a)))
##            1 (Cons a 0 y (Nil a))
## Cons a 2 x (Cons a 1 x (Cons a 0 y (Nil a))) :: Vec a 3


def plus(x: TermC, y: TermC) -> TermC:
    return Inf(Plus | app | x | app | y)


def bound(i: int) -> TermC:
    return Inf(Bound(i))


def vec(a: TermC, n: TermC) -> TermC:
    return Inf(Vec(a, n))


Append = Ann(
    Lam(
        Lam(
            Lam(
                Inf(
                    VecElim(
                        bound(2),
                        Lam(
                            Lam(
                                pi(
                                    Inf(Nat()),
                                    pi(
                                        vec(bound(5), bound(0)),
                                        vec(bound(6), plus(bound(3), bound(1))),
                                    ),
                                )
                            )
                        ),
                        Lam(Lam(bound(0))),
                        Lam(
                            Lam(
                                Lam(
                                    Lam(
                                        Lam(
                                            Lam(
                                                Inf(
                                                    Cons(
                                                        bound(8),
                                                        plus(bound(5), bound(1)),
                                                        bound(4),
                                                        Inf(
                                                            App(
                                                                App(Bound(2), bound(1)),
                                                                bound(0),
                                                            )
                                                        ),
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        ),
                        bound(1),
                        bound(0),
                    )
                )
            )
        )
    ),
    pi(
        Inf(Star()),
        pi(
            Inf(Nat()),
            pi(
                Inf(Vec(bound(1), bound(0))),
                pi(
                    Inf(Nat()),
                    pi(
                        Inf(Vec(bound(3), bound(0))),
                        Inf(Vec(bound(4), plus(bound(3), bound(1)))),
                    ),
                ),
            ),
        ),
    ),
)

print("Append=", Append)
print("type(Append)=", typeI0({}, Append))


env42: Context
env42 = {
    Global("a"): VStar(),
    Global("x"): VNeutral(NFree(Global("a"))),
    Global("y"): VNeutral(NFree(Global("a"))),
}
e42_v2 = Inf(
    Cons(
        free("a"),
        int2nat(1),
        free("x"),
        Inf(Cons(free("a"), int2nat(0), free("x"), Inf(Nil(free("a"))))),
    )
)
e42_v1 = Inf(Cons(free("a"), int2nat(0), free("y"), Inf(Nil(free("a")))))
e42_v3 = (
    Append
    | app
    | free("a")
    | app
    | int2nat(2)
    | app
    | e42_v2
    | app
    | int2nat(1)
    | app
    | e42_v1
)

print("e42_v3=", e42_v3)
print("type(ev42_v3)=", typeI0(env42, e42_v3))
print("eval(ev42_v3)=", evalI(e42_v3, []))
