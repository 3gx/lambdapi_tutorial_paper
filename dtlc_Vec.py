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


class ADT:
    class _MatchFail(Exception):
        pass

    _T = TTypeVar("_T")
    _U = TTypeVar("_U")

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

    def __enter__(self: _T) -> _T:
        return self

    def __exit__(self, type, value, traceback):  # type: ignore
        pass

    def __rshift__(self: _T, cls: TType[_U]) -> _U:
        if not isinstance(self, cls):
            raise ADT._MatchFail
        return self


import contextlib as ctxlib

_pm = ctxlib.suppress(ADT._MatchFail)


check_types = True
check_types = False
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
class Ann(ADT):
    e1: TermC
    e2: TermC

    def __repr__(self) -> str:
        return f"(Ann {self.e1}:{self.e2})"


@dataclass(**_dc_attrs)
class Star(ADT):
    def __repr__(self) -> str:
        return f"*"


@dataclass(**_dc_attrs)
class Pi(ADT):
    e1: TermC
    e2: TermC


@dataclass(**_dc_attrs)
class Bound(ADT):
    i: int

    def __repr__(self) -> str:
        return f"(Bound {self.i})"


@dataclass(**_dc_attrs)
class Free(ADT):
    x: Name

    def __repr__(self) -> str:
        return f"(Free {self.x})"


@dataclass(**_dc_attrs)
class App(ADT):
    e1: TermI
    e2: TermC


@dataclass(**_dc_attrs)
class Nat(ADT):
    def __repr__(self) -> str:
        return "Nat"


@dataclass(**_dc_attrs)
class NatElim(ADT):
    e1: TermC
    e2: TermC
    e3: TermC
    e4: TermC


@dataclass(**_dc_attrs)
class Zero(ADT):
    def __repr__(self) -> str:
        return "Zero"


@dataclass(**_dc_attrs)
class Succ(ADT):
    k: TermC

    def __repr__(self) -> str:
        return f"(Succ {self.k})"


@dataclass(**_dc_attrs)
class Vec(ADT):
    a: TermC
    n: TermC

    def __repr__(self) -> str:
        return f"(Vec {self.a} {self.n})"


@dataclass(**_dc_attrs)
class Nil(ADT):
    a: TermC

    def __repr__(self) -> str:
        return f"(Nil {self.a})"


@dataclass(**_dc_attrs)
class Cons(ADT):
    a: TermC
    n: TermC
    x: TermC
    xs: TermC

    def __repr__(self) -> str:
        return f"(Cons {self.a} {self.n} {self.x} {self.xs})"


@dataclass(**_dc_attrs)
class VecElim(ADT):
    a: TermC
    m: TermC
    mn: TermC
    mc: TermC
    n: TermC
    xs: TermC


TermC = TUnion["Inf", "Lam"]


@dataclass(**_dc_attrs)
class Inf(ADT):
    e: TermI

    def __repr__(self) -> str:
        return f"Inf({self.e})"


@dataclass(**_dc_attrs)
class Lam(ADT):
    e: TermC


Name = TUnion["Global", "Local", "Quote"]


@dataclass(**_dc_attrs)
class Global(ADT):
    str_: str

    def __repr__(self) -> str:
        return f"Global('{self.str_}')"

@dataclass(**_dc_attrs)
class Local(ADT):
    i: int


@dataclass(**_dc_attrs)
class Quote(ADT):
    i: int


_VFunT0 = TLam[["Value"], "Value"]
_VFunT = TUnion[Box[_VFunT0], _VFunT0]


@dataclass(**_dc_attrs)
class VLam(ADT):
    f: _VFunT

    def __repr__(self) -> str:
        return f"{quote0(self)}"


@dataclass(**_dc_attrs)
class VNeutral(ADT):
    n: Neutral


@dataclass(**_dc_attrs)
class VStar(ADT):
    def __repr__(self) -> str:
        return f"*"


@dataclass(**_dc_attrs)
class VPi(ADT):
    v: Value
    f: _VFunT

    def __repr__(self) -> str:
        return f"{quote0(self)}"


@dataclass(**_dc_attrs)
class VNat(ADT):
    pass


@dataclass(**_dc_attrs)
class VZero(ADT):
    pass


@dataclass(**_dc_attrs)
class VSucc(ADT):
    k: Value

    def __repr__(self) -> str:
        return f"{quote0(self)}"


@dataclass(**_dc_attrs)
class VNil(ADT):
    a: Value

    def __repr__(self) -> str:
        return f"{quote0(self)}"


@dataclass(**_dc_attrs)
class VCons(ADT):
    a: Value
    n: Value
    x: Value
    xs: Value

    def __repr__(self) -> str:
        return f"{quote0(self)}"


@dataclass(**_dc_attrs)
class VVec(ADT):
    a: Value
    n: Value

    def __repr__(self) -> str:
        return f"{quote0(self)}"


Value = TUnion[VLam, VNeutral, VStar, VPi, VNat, VZero, VSucc, VNil, VCons, VVec]


Neutral = TUnion["NFree", "NApp", "NNatElim", "NVecElim"]


@dataclass(**_dc_attrs)
class NFree(ADT):
    x: Name


@dataclass(**_dc_attrs)
class NApp(ADT):
    n: Neutral
    v: Value


@dataclass(**_dc_attrs)
class NNatElim(ADT):
    a: Value
    n: Value
    x: Value
    xs: Neutral


@dataclass(**_dc_attrs)
class NVecElim(ADT):
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
    with _pm, term >> Ann as (e, _):
        return evalC(e, env)
    with _pm, term >> Free as (x,):
        return vfree(x)
    with _pm, term >> Bound as (i,):
        return env[i]
    with _pm, term >> App as (e, e1):
        return vapp(evalI(e, env), evalC(e1, env))
    with _pm, term >> Star:
        return VStar()
    with _pm, term >> Pi as (t, t1):
        return VPi(evalC(t, env), lambda x: evalC(t1, [x] + env))
    with _pm, term >> Nat:
        return VNat()
    with _pm, term >> Zero:
        return VZero()
    with _pm, term >> Succ as (k,):
        return VSucc(evalC(k, env))
    with _pm, term >> NatElim as (m, mz, ms, k):
        mzVal = evalC(mz, env)
        msVal = evalC(ms, env)

        def rec1(kVal: Value) -> Value:
            with _pm, kVal >> VZero:
                return mzVal
            with _pm, kVal >> VSucc as (k,):
                return vapp(vapp(msVal, k), rec1(k))
            with _pm, kVal >> VNeutral as (n,):
                return VNeutral(NNatElim(evalC(m, env), mzVal, msVal, n))
            raise TypeError(f"Unknown instance '{type(kVal)}'")

        return rec1(evalC(k, env))
    with _pm, term >> Vec as (a, n):
        return VVec(evalC(a, env), evalC(n, env))
    with _pm, term >> Nil as (a,):
        return VNil(evalC(a, env))
    with _pm, term >> Cons as (a, n, x, xs):
        return VCons(evalC(a, env), evalC(n, env), evalC(x, env), evalC(xs, env))
    with _pm, term >> VecElim as (a, m, mn, mc, n, xs):
        mnVal = evalC(mn, env)
        mcVal = evalC(mc, env)

        def rec2(nVal: Value, xsVal: Value) -> Value:
            with _pm, xsVal >> VNil:
                return mnVal
            with _pm, xsVal >> VCons as (_, l, x, xs):
                return fold(vapp, [l, x, xs, rec2(l, xs)], mcVal)
            with _pm, xsVal >> VNeutral as (n,):
                return VNeutral(
                    NVecElim(evalC(a, env), evalC(m, env), mnVal, mcVal, nVal, n)
                )
            raise TypeError(f"Unknown instance '{type(xsVal)}'")

        return rec2(evalC(n, env), evalC(xs, env))
    raise TypeError(f"Unknown instance '{type(term)}'")


def vapp(value: Value, v: Value) -> Value:
    with _pm, value >> VLam as (f,):
        return f(v)
    with _pm, value >> VNeutral as (n,):
        return VNeutral(NApp(n, v))
    raise TypeError(f"Unknown instance '{type(v)}'")


def evalC(term: TermC, env: Env) -> Value:
    with _pm, term >> Inf as (e,):
        return evalI(e, env)
    with _pm, term >> Lam as (lam_expr,):
        return VLam(lambda x: evalC(lam_expr, [x] + env))
    raise TypeError(f"Unknown instance '{type(term)}'")


def typeI0(c: Context, term: TermI) -> Type:
    check_argument_types()
    return typeI(0, c, term)


def typeI(i: int, c: Context, term: TermI) -> Type:
    #    with _pm, Ann|term as p:
    #        reveal_type(p)
    with _pm, term >> Ann as (e1, e2):
        typeC(i, c, e2, VStar())
        t = evalC(e2, [])
        typeC(i, c, e1, t)
        return t
    with _pm, term >> Free as (x,):
        return c[x]
    with _pm, term >> App as (e1, e2):
        s = typeI(i, c, e1)
        with _pm, s >> VPi as (v, f):
            typeC(i, c, e2, v)
            return f(evalC(e2, []))
        raise TypeError(f"Illegal application: {e1}({e2})")
    with _pm, term >> Star:
        return VStar()
    with _pm, term >> Pi as (p, p1):
        typeC(i, c, p, VStar())
        t = evalC(p, [])
        typeC(i + 1, {Local(i): t, **c}, substC(0, Free(Local(i)), p1), VStar())
        return VStar()
    with _pm, term >> Nat:
        return VStar()
    with _pm, term >> Zero:
        return VNat()
    with _pm, term >> Succ:
        return VNat()
    with _pm, term >> NatElim as (m, mz, ms, k):
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
    with _pm, term >> Vec as (a, n):
        typeC(i, c, a, VStar())
        typeC(i, c, n, VNat())
        return VStar()
    with _pm, term >> Nil as (a,):
        typeC(i, c, a, VStar())
        aVal = evalC(a, [])
        return VVec(aVal, VZero())
    with _pm, term >> Cons as (a, k, x, xs):
        typeC(i, c, a, VStar())
        aVal = evalC(a, [])
        typeC(i, c, k, VNat())
        kVal = evalC(k, [])
        typeC(i, c, x, aVal)
        typeC(i, c, xs, VVec(aVal, kVal))
        return VVec(aVal, VSucc(kVal))
    with _pm, term >> VecElim as (a, m, mn, mc, k, vs):
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
    with _pm, term >> Inf as (e,):
        v = type_
        vp = typeI(i, c, e)
        if quote0(v) != quote0(vp):
            raise TypeError(f"type mismatch: {quote0(v)} != {quote0(vp)}")
        return
    with _pm, term >> Lam as (e,), type_ >> VPi as (t, tp):
        typeC(
            i + 1,
            {Local(i): t, **c},
            substC(0, Free(Local(i)), e),
            tp(vfree(Local(i))),
        )
        return
    raise TypeError(f"Type mismatch: term={type(term)}', type={type(type_)}")


def substI(i: int, r: TermI, t: TermI) -> TermI:
    with _pm, t >> Ann as (e1, e2):
        e1, e2 = t
        return Ann(substC(i, r, e1), e2)
    with _pm, t >> Bound as (j,):
        return r if i == j else Bound(j)
    with _pm, t >> Free:
        return t
    with _pm, t >> App as (e1, e2):
        return App(substI(i, r, e1), substC(i, r, e2))
    with _pm, t >> Star:
        return Star()
    with _pm, t >> Pi as (f, v):
        return Pi(substC(i, r, f), substC(i + 1, r, v))
    with _pm, t >> Nat:
        return Nat()
    with _pm, t >> Zero:
        return Zero()
    with _pm, t >> Succ as (k,):
        return Succ(substC(i, r, k))
    with _pm, t >> NatElim as (m, mz, ms, k):
        return NatElim(
            substC(i, r, m), substC(i, r, mz), substC(i, r, ms), substC(i, r, k)
        )
    with _pm, t >> Vec as (a, n):
        return Vec(substC(i, r, a), substC(i, r, n))
    with _pm, t >> Nil as (a,):
        return Nil(substC(i, r, a))
    with _pm, t >> Cons as (a, n, x, xs):
        return Cons(substC(i, r, a), substC(i, r, n), substC(i, r, x), substC(i, r, xs))
    with _pm, t >> VecElim as (a, m, mn, mc, n, xs):
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
    with _pm, t >> Inf as (e,):
        return Inf(substI(i, r, e))
    with _pm, t >> Lam as (e,):
        return Lam(substC(i + 1, r, e))
    raise TypeError(f"Unknown instance '{type(t)}'")


def quote0(v: Value) -> TermC:
    check_argument_types()
    return quote(0, v)


def quote(i: int, value: Value) -> TermC:
    with _pm, value >> VLam as (f,):
        return Lam(quote(i + 1, f(vfree(Quote(i)))))
    with _pm, value >> VNeutral as (n,):
        return Inf(neutralQuote(i, n))
    with _pm, value >> VStar:
        return Inf(Star())
    with _pm, value >> VPi as (v, f):
        return Inf(Pi(quote(i, v), quote(i + 1, f(vfree(Quote(i))))))
    with _pm, value >> VNat:
        return Inf(Nat())
    with _pm, value >> VZero:
        return Inf(Zero())
    with _pm, value >> VSucc as (k,):
        return Inf(Succ(quote(i, k)))
    with _pm, value >> VNil as (a,):
        return Inf(Nil(quote(i, a)))
    with _pm, value >> VVec as (a, n):
        return Inf(Vec(quote(i, a), quote(i, n)))
    with _pm, value >> VCons as (a, n, x, xs):
        return Inf(Cons(quote(i, a), quote(i, n), quote(i, x), quote(i, xs)))
    raise TypeError(f"Unknown instance '{type(value)}'")


def neutralQuote(i: int, neutral: Neutral) -> TermI:
    with _pm, neutral >> NFree as (x,):
        return boundfree(i, x)
    with _pm, neutral >> NApp as (n, v):
        return App(neutralQuote(i, n), quote(i, v))
    with _pm, neutral >> NNatElim as (a, n, x, xs):
        return NatElim(quote(i, a), quote(i, n), quote(i, x), Inf(neutralQuote(i, xs)))
    with _pm, neutral >> NVecElim as (a, m, mn, mc, n, xs):
        return VecElim(
            quote(i, a),
            quote(i, m),
            quote(i, mn),
            quote(i, mc),
            quote(i, n),
            Inf(neutralQuote(i, xs)),
        )
    raise TypeError(f"Unknown instance '{type(neutral)}'")


def boundfree(i: int, x: Name) -> TermI:
    check_argument_types()
    with _pm, x >> Quote as (k,):
        return Bound(i - k - 1)
    return Free(x)


###############################################################################
# Examples
###############################################################################

def vapply(f: Value, args: TList[Value]) -> Value:
    for arg in args:
        f = vapp(f, arg)
    return f


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

natElimL = Lam(
    Lam(
        Lam(
            Lam(
                Inf(NatElim(Inf(Bound(3)), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0))))
            )
        )
    )
)
natElimTy = VPi(
    VPi(VNat(), lambda _: VStar()),
    lambda m: VPi(
        vapp(m, VZero()),
        lambda _: VPi(
            VPi(VNat(), lambda k: VPi(vapp(m, k), lambda _: vapp(m, VSucc(k)))),
            lambda _: VPi(VNat(), lambda n: vapp(m, n)),
        ),
    ),
)

natElim = Ann(natElimL, quote0(natElimTy))
print("natElim=", natElim)
print("type(natElim)=", typeI0({}, natElim))
Plus = App(
    App(App(natElim, Lam(pi(Inf(Nat()), Inf(Nat())))), Lam(Inf(Bound(0)))),
    Lam(Lam(Lam(Inf(Succ(Inf(App(Bound(1), Inf(Bound(0))))))))),
)
VnatElim = evalI(natElim, [])
vplus = vapply(VnatElim, [\
        VLam(lambda _: VPi(VNat(), lambda _ : VNat())),
        VLam(lambda n : n),
        VLam(lambda p: VLam(lambda rec: VLam(lambda n : VSucc(vapp(rec, n)))))])
print("vplus=", vplus)
#Plus2 : TermI
#plus2env : Context
#plus2env = {Global("VnatElim"): natElimTy}
#Plus2, _ = (quote0(vplus) >> Inf).e >> App
#print("plus2env=", plus2env)
#print("Plus2=",Plus2)
#print("type(Plus2)=", typeI0(plus2env, Plus2))

Plus1 = Ann(
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
    with _pm, v >> VZero:
        return 0
    with _pm, v >> VSucc as (k,):
        return 1 + nval2int(k)
    raise TypeError(f"Unknown instance '{type(v)}'")



#e1 = evalI(App(App(Plus2, int2nat(2)), int2nat(2)), [])
#print("e1= ", e1)
#print("2+2 ->", nval2int(evalI(App(App(Plus, int2nat(2)), int2nat(2)), [])))
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
##        :: Pi (a :: *) (m :: Nat) (v :: Vec a m) (n :: Nat) (w :: Vec a n) .
##           Vec a (plus m n)

## > assume (a :: *) (x :: a) (y :: a)
## > append a 2 (Cons a 1 x (Cons a 0 x (Nil a)))
##            1 (Cons a 0 y (Nil a))
## Cons a 2 x (Cons a 1 x (Cons a 0 y (Nil a))) :: Vec a 3


def plus(x: TermC, y: TermC) -> TermC:
    return Inf(App(App(Plus, x), y))


def bound(i: int) -> TermC:
    return Inf(Bound(i))


def vec(a: TermC, n: TermC) -> TermC:
    return Inf(Vec(a, n))


vecElimL = Lam(
    Lam(
        Lam(
            Lam(
                Lam(
                    Lam(
                        Inf(
                            VecElim(
                                Inf(Bound(5)),
                                Inf(Bound(4)),
                                Inf(Bound(3)),
                                Inf(Bound(2)),
                                Inf(Bound(1)),
                                Inf(Bound(0)),
                            )
                        )
                    )
                )
            )
        )
    )
)



vecElimTy = VPi(
    VStar(),
    lambda a: VPi(
        VPi(VNat(), lambda n: VPi(VVec(a, n), lambda _: VStar())),
        lambda m: VPi(
            vapp(vapp(m, VZero()), VNil(a)),
            lambda _: VPi(
                VPi(
                    VNat(),
                    lambda n: VPi(
                        a,
                        lambda x: VPi(
                            VVec(a, n),
                            lambda xs: VPi(
                                vapp(vapp(m, n), xs),
                                lambda _: vapp(vapp(m, VSucc(n)), VCons(a, n, x, xs)),
                            ),
                        ),
                    ),
                ),
                lambda _: VPi(
                    VNat(), lambda n: VPi(VVec(a, n), lambda xs: vapp(vapp(m, n), xs))
                ),
            ),
        ),
    ),
)
vecElim = Ann(vecElimL, quote0(vecElimTy))
print("vecElim=", vecElim)
print("type(vecElim)", typeI0({}, vecElim))
AppendE = Lam(
    Inf(
        App(
            App(
                App(
                    App(vecElim, bound(0)),
                    Lam(
                        Lam(
                            pi(
                                Inf(Nat()),
                                pi(
                                    vec(bound(3), bound(0)),
                                    vec(bound(4), plus(bound(3), bound(1))),
                                ),
                            )
                        )
                    ),
                ),
                Lam(Lam(bound(0))),
            ),
            Lam(
                Lam(
                    Lam(
                        Lam(
                            Lam(
                                Lam(
                                    Inf(
                                        Cons(
                                            bound(6),
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
        )
    )
)


vplus = evalI(Plus, [])
vvecelim = evalI(vecElim, [])
AppendTy = VPi(
    VStar(),
    lambda a: VPi(
        VNat(),
        lambda m: VPi(
            VVec(a, m),
            lambda v: VPi(
                VNat(),
                lambda n: VPi(VVec(a, n), lambda w: VVec(a, vapp(vapp(vplus, m), n))),
            ),
        ),
    ),
)
print("AppenTy=", quote0(AppendTy))
VVecElim = evalI(vecElim, [])
append = Ann(AppendE, quote0(AppendTy))
print("type(append)= ", typeI0({}, append))
VAppend = VLam(
    lambda a: vapply(
        VVecElim,
        [
            a,
            VLam(
                lambda m: VLam(
                    lambda _: VPi(
                        VNat(),
                        lambda n: VPi(
                            VVec(a, n), lambda _: VVec(a, vapply(vplus, [m, n]))
                        ),
                    )
                )
            ),
            VLam(lambda _: VLam(lambda v: v)),
            VLam(
                lambda m: VLam(
                    lambda v: VLam(
                        lambda vs: VLam(
                            lambda rec: VLam(
                                lambda n: VLam(
                                    lambda w: VCons(
                                        a, vapply(vplus, [m, n]), v, vapply(rec, [n, w])
                                    )
                                )
                            )
                        )
                    )
                )
            ),
        ],
    )
)
AppendC = quote0(VAppend)
print("AppendC=", AppendC)
# sys.exit(0)
# print("append=", append)
Append = Ann(AppendC, quote0(AppendTy))
_Append = Ann(
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
e42_v3 = App(
    App(App(App(App(Append, free("a")), int2nat(2)), e42_v2), int2nat(1)), e42_v1
)

print("e42_v3=", e42_v3)
print("type(ev42_v3)=", typeI0(env42, e42_v3))
print("eval(ev42_v3)=", evalI(e42_v3, []))

import time

t1 = time.time()
for i in range(1000):
    evalI(e42_v3, [])
t2 = time.time()
print(t2 - t1)
