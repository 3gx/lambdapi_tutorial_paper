# run 'mypy' on this source tree, e.g. form the root repo folder, run
# ```
# $ mypy
# Success: no issues found in 4 source files
# ```
# see mypy.ini for configuration

from __future__ import annotations

import typing as ty
from typing import Any as TAny, Callable as TLam, List as TList, \
                   Dict as TDict, Union as TUnion, Type as TType, \
                   TypeVar as TTypeVar, Generic as TGeneric, Tuple as TTuple
import sys
from dataclasses import dataclass
import dataclasses as dc
import functools
from functools import reduce as fold
#import operator
#foldl = lambda func, acc, xs: functools.reduce(func, xs, acc)

_dc_attrs = {"frozen": True}


# --start-of-war--  mypy issue: https://github.com/python/mypy/issues/5485
_BoxT = TTypeVar("_BoxT")
@dataclass
class Box(TGeneric[_BoxT]):
    inner: _BoxT
    @property
    def __call__(self) -> _BoxT:
        return self.inner
# --end-of-war--

@dataclass(**_dc_attrs)
class TermI:
    pass
@dataclass(**_dc_attrs)
class Ann(TermI):
    e1 : TermC
    e2 : TermC
@dataclass(**_dc_attrs)
class Star(TermI):
    def __repr__(self) -> str:
        return f"*"
@dataclass(**_dc_attrs)
class Pi(TermI):
    e1 : TermC
    e2 : TermC
    def __repr__(self) -> str:
        return f"(Pi {self.e1} {self.e2})"
@dataclass(**_dc_attrs)
class Bound(TermI):
    i : int
    def __repr__(self) -> str:
        return f"(Bound {self.i})"
@dataclass(**_dc_attrs)
class Free(TermI):
    x : Name
    def __repr__(self) -> str:
        return f"{self.x}"
@dataclass(**_dc_attrs)
class App(TermI):
    e1 : TermI
    e2 : TermC
@dataclass(**_dc_attrs)
class Nat(TermI):
    def __repr__(self) -> str:
        return "Nat"
@dataclass(**_dc_attrs)
class NatElim(TermI):
    e1 : TermC
    e2 : TermC
    e3 : TermC
    e4 : TermC
@dataclass(**_dc_attrs)
class Zero(TermI):
    def __repr__(self) -> str:
        return "Zero"
@dataclass(**_dc_attrs)
class Succ(TermI):
    k : TermC
    def __repr__(self) -> str:
        return f"(Succ {self.k})"

@dataclass(**_dc_attrs)
class Vec(TermI):
    a : TermC
    n : TermC

@dataclass(**_dc_attrs)
class Nil(TermI):
    a : TermC
    def __repr__(self) -> str:
        return f"(Nil {self.a})"

@dataclass(**_dc_attrs)
class Cons(TermI):
    a : TermC
    n : TermC
    x : TermC
    xs : TermC

@dataclass(**_dc_attrs)
class VecElim(TermI):
    a : TermC
    m : TermC
    mn : TermC
    mc : TermC
    n : TermC
    xs : TermC

@dataclass(**_dc_attrs)
class TermC:
    pass
@dataclass(**_dc_attrs)
class Inf(TermC):
    e : TermI
    def __repr__(self) -> str:
        return f"{self.e}"
@dataclass(**_dc_attrs)
class Lam(TermC):
    e : TermC

@dataclass(**_dc_attrs)
class Name():
    pass
@dataclass(**_dc_attrs)
class Global(Name):
    str_ : str
    def __repr__(self) -> str:
        return f"(Global '{self.str_}')"

@dataclass(**_dc_attrs)
class Local(Name):
    i : int
@dataclass(**_dc_attrs)
class Quote(Name):
    i : int

@dataclass(**_dc_attrs)
class Value:
    def __repr__(self) -> str:
        return f"{quote0(self)}"
_VFunT0 = TLam[[Value], Value]
_VFunT = TUnion[Box[_VFunT0], _VFunT0]
@dataclass(**_dc_attrs)
class VLam(Value):
    f : _VFunT
    def __repr__(self) -> str:
        return super().__repr__()
@dataclass(**_dc_attrs)
class VNeutral(Value):
    n : Neutral
    def __repr__(self) -> str:
        return super().__repr__()
@dataclass(**_dc_attrs)
class VStar(Value):
    def __repr__(self) -> str:
        return super().__repr__()
@dataclass(**_dc_attrs)
class VPi(Value):
    v : Value
    f : _VFunT
    def __repr__(self) -> str:
        return super().__repr__()
@dataclass(**_dc_attrs)
class VNat(Value):
    def __repr__(self) -> str:
        return super().__repr__()
@dataclass(**_dc_attrs)
class VZero(Value):
    def __repr__(self) -> str:
        return super().__repr__()
@dataclass(**_dc_attrs)
class VSucc(Value):
    k : Value
    def __repr__(self) -> str:
        return super().__repr__()
@dataclass(**_dc_attrs)
class VNil(Value):
    a : Value
@dataclass(**_dc_attrs)
class VCons(Value):
    a : Value
    n : Value
    x : Value
    xs : Value
@dataclass(**_dc_attrs)
class VVec(Value):
    a : Value
    n : Value


@dataclass(**_dc_attrs)
class Neutral:
    pass
@dataclass(**_dc_attrs)
class NFree(Neutral):
    x : Name
@dataclass(**_dc_attrs)
class NApp(Neutral):
    n : Neutral
    v : Value
@dataclass(**_dc_attrs)
class NNatElim(Neutral):
    a  : Value
    n  : Value
    x  : Value
    xs : Neutral
@dataclass(**_dc_attrs)
class NVecElim(Neutral):
    v1 : Value
    v2 : Value
    v3 : Value
    v4 : Value
    v5 : Value
    n  : Neutral

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
    elif isinstance(term, Nat):
        return VNat()
    elif isinstance(term, Zero):
        return VZero()
    elif isinstance(term, Succ):
        return VSucc(evalC(term.k, env))
    elif isinstance(term, NatElim):
        def unpack(obj : TAny) -> TTuple[TAny, ...]:
            return tuple(getattr(obj, field.name) for field in dc.fields(obj))
        m, mz, ms, k = unpack(term)
        mzVal = evalC(mz, env)
        msVal = evalC(ms, env)
        def rec1(kVal : Value) -> Value:
            if isinstance(kVal, VZero):
                return mzVal
            elif isinstance(kVal, VSucc):
                return vapp(vapp(msVal, kVal.k), rec1(kVal.k))
            elif isinstance(kVal, VNeutral):
                return VNeutral(NNatElim(evalC(m,env), mzVal, msVal, kVal.n))
            raise TypeError(f"Unknown instance '{type(kVal)}'")
        return rec1(evalC(k, env))
    elif isinstance(term, Vec):
        return VVec(evalC(term.a, env), evalC(term.n, env))
    elif isinstance(term, Nil):
        return VNil(evalC(term.a, env))
    elif isinstance(term, Cons):
        return VCons(evalC(term.a, env), evalC(term.n, env),
                     evalC(term.x, env), evalC(term.xs, env))
    elif isinstance(term, VecElim):
        mnVal = evalC(term.mn, env)
        mcVal = evalC(term.mc, env)
        a,m,mn,mc,n,xs = (term.a, term.m, term.mn, term.mc, term.n, term.xs)
        def rec2(nVal : Value, xsVal : Value) -> Value:
            if isinstance(xsVal, VNil):
                return mnVal
            elif isinstance(xsVal, VCons):
                l,x,xs = (xsVal.n, xsVal.x, xsVal.xs)
                return fold(vapp, [l,x,xs,rec2(l,xs)], mcVal)
            elif isinstance(xsVal, VNeutral):
                return VNeutral(NVecElim(evalC(a, env),
                                         evalC(m, env),
                                         mnVal, mcVal, nVal, xsVal.n))
            raise TypeError(f"Unknown instance '{type(xsVal)}'")

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
    elif isinstance(term, Nat):
        return VStar()
    elif isinstance(term, Zero):
        return VNat()
    elif isinstance(term, Succ):
        return VNat()
    elif isinstance(term, NatElim):
        m, mz, ms, k = (term.e1, term.e2, term.e3, term.e4)
        typeC(i,c,m,VPi(VNat(), lambda _ : VStar()))
        mVal = evalC(m, [])
        typeC(i,c,mz, vapp(mVal, VZero()))
        typeC(i,c,ms,
                VPi(VNat(),
                    lambda l : VPi(vapp(mVal,l),
                                   lambda _ : vapp(mVal, VSucc(l)))))
        typeC(i, c, k, VNat())
        kVal = evalC(k, [])
        return vapp(mVal, kVal)
    elif isinstance(term, Vec):
        typeC(i,c,term.a, VStar())
        typeC(i,c,term.n, VNat())
        return VStar()
    elif isinstance(term, Nil):
        typeC(i,c,term.a, VStar())
        aVal = evalC(term.a, [])
        return VVec(aVal, VZero())
    elif isinstance(term, Cons):
        typeC(i,c,term.a, VStar())
        aVal = evalC(term.a, [])
        typeC(i,c,term.n, VNat())
        kVal = evalC(term.n, [])
        typeC(i,c,term.x, aVal)
        typeC(i,c,term.xs, VVec(aVal, kVal))
        return VVec(aVal, VSucc(kVal))
    elif isinstance(term, VecElim):
        a,m,mn,mc,k,vs = (term.a, term.m, term.mn, term.mc, term.n, term.xs)
        typeC(i,c,a,VStar())
        aVal = evalC(a, [])
        typeC(i,c,m, VPi(VNat(), lambda k : VPi(VVec(aVal,k),
                                     lambda _ : VStar())))
        mVal = evalC(m, [])
        typeC(i,c,mn, fold(vapp, [VZero(), VNil(aVal)], mVal))
        typeC(i,c,mc,
                VPi(VNat(), lambda l:
                    VPi(aVal, lambda y:
                        VPi(VVec(aVal,l), lambda ys:
                            VPi(fold(vapp, [l,ys], mVal), lambda _:
                                fold(vapp, [VSucc(l), VCons(aVal,l,y,ys)],
                                    mVal))))))
        typeC(i,c,k,VNat())
        kVal = evalC(k, [])
        typeC(i,c,vs,VVec(aVal,kVal))
        vsVal = evalC(vs, [])
        return fold(vapp, [kVal, vsVal], mVal)
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
    raise TypeError(f"Type mismatch: term={type(term)}', type={type(type)}")

def substI(i : int, r : TermI, t : TermI) -> TermI:
    if isinstance(t, Ann):
        return Ann(substC(i,r,t.e1), t.e2)
    elif isinstance(t, Bound):
        return r if i == t.i else t
    elif isinstance(t, Free):
        return t
    elif isinstance(t, App):
        return App(substI(i,r,t.e1), substC(i,r,t.e2))
    elif isinstance(t, Star):
        return Star()
    elif isinstance(t, Pi):
        return Pi(substC(i,r,t.e1), substC(i+1, r, t.e2))
    elif isinstance(t, Nat):
        return Nat()
    elif isinstance(t, Zero):
        return Zero()
    elif isinstance(t, Succ):
        return Succ(substC(i,r,t.k))
    elif isinstance(t, NatElim):
        m, mz, ms, k = (t.e1, t.e2, t.e3, t.e4)
        return NatElim(substC(i,r,m),
                       substC(i,r,mz),
                       substC(i,r,ms),
                       substC(i,r,k))
    elif isinstance(t, Vec):
        return Vec(substC(i,r,t.a), substC(i,r,t.n))
    elif isinstance(t, Nil):
        return Nil(substC(i,r,t.a))
    elif isinstance(t, Cons):
        return Cons(substC(i,r,t.a), substC(i,r,t.n),
                    substC(i,r,t.x), substC(i,r,t.xs))
    elif isinstance(t,VecElim):
        a,m,mn,mc,n,xs = (t.a, t.m, t.mn, t.mc, t.n, t.xs)
        return VecElim(substC(i,r,a), substC(i,r,m),
                       substC(i,r,mn), substC(i,r,mc),
                       substC(i,r,n), substC(i,r,xs))
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
    elif isinstance(v, VNat):
        return Inf(Nat())
    elif isinstance(v, VZero):
        return Inf(Zero())
    elif isinstance(v, VSucc):
        return Inf(Succ(quote(i,v.k)))
    elif isinstance(v, VNil):
        return Inf(Nil(quote(i,v.a)))
    elif isinstance(v, VVec):
        return Inf(Vec(quote(i,v.a), quote(i,v.n)))
    elif isinstance(v, VCons):
        return Inf(Cons(quote(i,v.a), quote(i,v.n),
                        quote(i,v.x), quote(i,v.xs)))
    raise TypeError(f"Unknown instance '{type(v)}'")

def neutralQuote(i : int, n : Neutral) -> TermI:
    if isinstance(n, NFree):
        return boundfree(i,n.x)
    elif isinstance(n, NApp):
        return App(neutralQuote(i, n.n), quote(i,n.v))
    elif isinstance(n, NNatElim):
        return NatElim(quote(i,n.a), quote(i,n.n),
                       quote(i,n.x), Inf(neutralQuote(i,n.xs)))
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

print("eval(term1)=", evalI(term1, []))
print("qeval(term1)=", quote0(evalI(term1, [])))
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

## > let plus = natElim (\_ -> Nat -> Nat)
##                      (\n -> n)
##                      (\k rec n -> Succ (rec n))
## plus :: Pi (x :: Nat) (y :: Nat) . Nat

plus : TLam[[TermC], TermI] = lambda x : NatElim(
        Lam(pi(Inf(Nat()),Inf(Nat()))),
        Lam(Inf(Bound(0))),
        Lam(
          Lam(
            Lam(
              Inf(
                Succ (Inf (App(Bound(1), Inf(Bound(0)))))
              )
            )
          )
        ),
        x
       )
plusx = Ann(Lam(Inf(NatElim(
        Lam(pi(Inf(Nat()),Inf(Nat()))),
        Lam(Inf(Bound(0))),
        Lam(
          Lam(
            Lam(
              Inf(
                Succ (Inf (App(Bound(1), Inf(Bound(0)))))
              )
            )
          )
        ),
        Inf(Bound(0))
       ))), pi(Inf(Nat()), pi(Inf(Nat()), Inf(Nat()))))
print("type(plusx)=", typeI0({}, plusx))

def int2nat(n : int) -> TermC:
    if n == 0:
        return Inf(Zero())
    else:
        return Inf(Succ(int2nat(n-1)))

def nval2int(v : Value) -> int:
    if isinstance(v, VZero):
        return 0
    elif isinstance(v, VSucc):
        return 1 + nval2int(v.k)
    raise TypeError(f"Unknown instance '{type(v)}'")

print("2+2 ->", nval2int(evalI(App(App(plusx, int2nat(2)), int2nat(2)),[])))
#sys.exit(0)

## > plus 40 2
## 42 :: Nat
n40 = int2nat(40)
print("n40=", n40)
n2  = int2nat(2)
print("n2=", n2)
print("type(n40)=", typeI0({},ty.cast(Inf,n40).e))
print("type(plus(n40))=", typeI0({},plus(n40)))
n42term = App(plus(n40),n2)
print("type(n42term)=", typeI0({}, n42term))
n42v = evalI(n42term, [])
print("n42v=", n42v)
n42 = nval2int(n42v)
print("n42=", n42)
## > n42
## 42

from functools import partial

class Infix(object):
    T = TTypeVar("T")
    U = TTypeVar("U")
    R = TTypeVar("R")
    def __init__(self, func : TUnion[TLam[[U],R], TLam[[T,U],R]]):
        self.func = func
    def __or__(self, other : U) -> R:
        return ty.cast(TLam[[Infix.U],Infix.R],self.func)(other)
    def __ror__(self, other : T) -> Infix:
        return Infix(partial(self.func, other)) #type: ignore

@Infix
def app(x : TermI, y : TermC) -> TermI:
    return App(x,y)

n1 = int2nat(1)
n2a : TermI = plus(n1) |app| n1
print("n2a=", n2a)
print("type(n2a)=", typeI0({}, n2a))
n2e = evalI(n2a, [])
print("n2e=", n2e)
print("n2e=", nval2int(n2e))
n4 = App(plus(Inf(n2a)), Inf(n2a))
print("n4=", n4, type(n4).__class__)
print("type(n4)=", typeI0({}, n4))
print("eval(n4)=", nval2int(evalI(n4,[])))

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


def plus1(x : TermC, y : TermC) -> TermC:
    return Inf(App(plus(x),y))

def bound(i : int) -> TermC:
    return Inf(Bound(i))
def vec(a : TermC, n : TermC) -> TermC:
    return Inf(Vec(a,n))

def f_append(n : TermC, xs : TermC) -> TermI:
    return Pi(Inf(Star()), Inf(
             VecElim(
               bound(0),
               Lam(Lam(pi(Inf(Nat()),
                    pi(vec(bound(3),bound(0)),
                        vec(bound(4), plus1(bound(3),bound(1))))))),
               Lam(Lam(bound(0))),
               Lam(Lam(Lam(Lam(Lam(Lam(
                   Inf(Cons(bound(6),
                        plus1(bound(5), bound(1)),
                        bound(4),
                        Inf(App(App(Bound(2),bound(1)),bound(0))))))))))),
                   n, xs)))

env42 : Context
env42 = {Global("a"):VStar(),
         Global("x"):VNeutral(NFree(Global("a"))),
         Global("y"):VNeutral(NFree(Global("a")))}
v1 = Inf(Cons(free("a"),
          int2nat(1),
          free("x"),
          Inf(Cons(free("a"), int2nat(0), free("x"),
          Inf(Nil(free("a")))))))
append = f_append(int2nat(2), v1)
print("append=", append)
print("type(append)=", typeI0(env42,append))
#append_a = App(append,
