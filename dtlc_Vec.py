# run 'mypy' on this source tree, e.g. form the root repo folder, run
# ```
# $ mypy
# Success: no issues found in 4 source files
# ```
# see mypy.ini for configuration for mypy.
#

from __future__ import annotations

from typing import Any as TAny, Callable as TLam, List as TList, \
                   Dict as TDict, Union as TUnion, Type as TType, \
                   TypeVar as TTypeVar, Generic as TGeneric, Tuple as TTuple, \
                   cast as _cast
import sys
from mydataclasses import dataclass
import mydataclasses as dc
import typeguard
import functools
from functools import reduce as fold
foldl : TLam[[TAny, TAny, TAny], TAny] = lambda func, acc, xs: functools.reduce(func, xs, acc)

_dc_attrs = {"frozen": True}

check_types = True
#check_types = False
check_argument_types : TLam[[],bool]
if check_types:
    check_argument_types = typeguard.check_argument_types
else:
    check_argument_types = lambda : True

# --WAR-beg--  mypy issue: https://github.com/python/mypy/issues/5485
_BoxT = TTypeVar("_BoxT")
@dataclass
class Box(TGeneric[_BoxT]):
    inner: _BoxT # pytype: disable=not-supported-yet
    @property
    def __call__(self) -> _BoxT:
        return self.inner
# --WAR-end--


abstract = dataclass(frozen=True)


# mypy WAR for current lack of python forward declration, use strings :)
TermI = TUnion["Ann", "Star", "Pi", "Bound", "Free", "App", \
               "Nat", "NatElim", "Zero", "Succ", \
               "Vec", "Nil", "Cons", "VecElim"]
@dataclass(**_dc_attrs)
class Ann:
    e1 : TermC
    e2 : TermC
@dataclass(**_dc_attrs)
class Star:
    def __repr__(self) -> str:
        return f"*"
@dataclass(**_dc_attrs)
class Pi:
    e1 : TermC
    e2 : TermC
    def __repr__(self) -> str:
        return f"(Pi {self.e1} {self.e2})"
@dataclass(**_dc_attrs)
class Bound:
    i : int
    def __repr__(self) -> str:
        return f"(Bound {self.i})"
@dataclass(**_dc_attrs)
class Free:
    x : Name
    def __repr__(self) -> str:
        return f"{self.x}"
@dataclass(**_dc_attrs)
class App:
    e1:  TermI
    e2 : TermC
@dataclass(**_dc_attrs)
class Nat:
    def __repr__(self) -> str:
        return "Nat"
@dataclass(**_dc_attrs)
class NatElim:
    e1 : TermC
    e2 : TermC
    e3 : TermC
    e4 : TermC
@dataclass(**_dc_attrs)
class Zero:
    def __repr__(self) -> str:
        return "Zero"
@dataclass(**_dc_attrs)
class Succ:
    k : TermC
    def __repr__(self) -> str:
        return f"(Succ {self.k})"
@dataclass(**_dc_attrs)
class Vec:
    a : TermC
    n : TermC
    def __repr__(self) -> str:
        return f"(Vec {self.a} {self.n})"
@dataclass(**_dc_attrs)
class Nil:
    a : TermC
    def __repr__(self) -> str:
        return f"(Nil {self.a})"
@dataclass(**_dc_attrs)
class Cons:
    a : TermC
    n : TermC
    x : TermC
    xs : TermC
    def __repr__(self) -> str:
        return f"(Cons {self.a} {self.n} {self.x} {self.xs})"
@dataclass(**_dc_attrs)
class VecElim:
    a : TermC
    m : TermC
    mn : TermC
    mc : TermC
    n : TermC
    xs : TermC

TermC = TUnion["Inf", "Lam"]
@dataclass(**_dc_attrs)
class Inf:
    e : TermI
    def __repr__(self) -> str:
        return f"{self.e}"
@dataclass(**_dc_attrs)
class Lam:
    e : TermC


Name = TUnion["Global", "Local", "Quote"]
@dataclass(**_dc_attrs)
class Global:
    str_ : str
    def __repr__(self) -> str:
        return f"'{self.str_}'"
@dataclass(**_dc_attrs)
class Local:
    i : int
@dataclass(**_dc_attrs)
class Quote:
    i : int

_VFunT0 = TLam[["Value"], "Value"]
_VFunT = TUnion[Box[_VFunT0], _VFunT0]
@dataclass(**_dc_attrs)
class VLam:
    f : _VFunT
    def __repr__(self) -> str:
        return f"{quote0(self)}"
@dataclass(**_dc_attrs)
class VNeutral:
    n : Neutral
@dataclass(**_dc_attrs)
class VStar:
    def __repr__(self) -> str:
        return f"*"
@dataclass(**_dc_attrs)
class VPi:
    v : Value
    f : _VFunT
    def __repr__(self) -> str:
        return f"{quote0(self)}"
@dataclass(**_dc_attrs)
class VNat:
    pass
@dataclass(**_dc_attrs)
class VZero:
    pass
@dataclass(**_dc_attrs)
class VSucc:
    k : Value
    def __repr__(self) -> str:
        return f"{quote0(self)}"
@dataclass(**_dc_attrs)
class VNil:
    a : Value
    def __repr__(self) -> str:
        return f"{quote0(self)}"
@dataclass(**_dc_attrs)
class VCons:
    a : Value
    n : Value
    x : Value
    xs : Value
    def __repr__(self) -> str:
        return f"{quote0(self)}"
@dataclass(**_dc_attrs)
class VVec:
    a : Value
    n : Value
    def __repr__(self) -> str:
        return f"{quote0(self)}"

Value = TUnion[VLam, VNeutral, VStar, VPi, \
               VNat, VZero, VSucc, \
               VNil, VCons, VVec]


Neutral = TUnion["NFree", "NApp", "NNatElim", "NVecElim"]
@dataclass(**_dc_attrs)
class NFree:
    x : Name
@dataclass(**_dc_attrs)
class NApp:
    n : Neutral
    v : Value
@dataclass(**_dc_attrs)
class NNatElim:
    a  : Value
    n  : Value
    x  : Value
    xs : Neutral
@dataclass(**_dc_attrs)
class NVecElim:
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

def _unpack(obj : TAny) -> TTuple[TAny, ...]:
    return tuple(getattr(obj, field.name) for field in dc.fields(obj))

def evalI(term : TermI, env : Env) -> Value:
    check_argument_types()
    if isinstance(term, Ann):
        e, _ = _unpack(term)
        return evalC(e, env)
    elif isinstance(term, Free):
        x, = _unpack(term)
        return vfree(x)
    elif isinstance(term, Bound):
        i : int
        i, = _unpack(term)
        return env[i]
    elif isinstance(term, App):
        e, e1 = _unpack(term)
        return vapp(evalI(e, env), evalC(e1, env))
    elif isinstance(term, Star):
        return VStar()
    elif isinstance(term, Pi):
        t,t1 = _unpack(term)
        return VPi(evalC(t,env), lambda x: evalC(t1, [x] + env))
    elif isinstance(term, Nat):
        return VNat()
    elif isinstance(term, Zero):
        return VZero()
    elif isinstance(term, Succ):
        k, = _unpack(term)
        return VSucc(evalC(k, env))
    elif isinstance(term, NatElim):
        m, mz, ms, k = _unpack(term)
        mzVal = evalC(mz, env)
        msVal = evalC(ms, env)
        def rec1(kVal : Value) -> Value:
            check_argument_types()
            if isinstance(kVal, VZero):
                return mzVal
            elif isinstance(kVal, VSucc):
                return vapp(vapp(msVal, kVal.k), rec1(kVal.k))
            elif isinstance(kVal, VNeutral):
                return VNeutral(NNatElim(evalC(m,env), mzVal, msVal, kVal.n))
            raise TypeError(f"Unknown instance '{type(kVal)}'")
        return rec1(evalC(k, env))
    elif isinstance(term, Vec):
        a, n = _unpack(term)
        return VVec(evalC(a, env), evalC(n, env))
    elif isinstance(term, Nil):
        a, = _unpack(term)
        return VNil(evalC(a, env))
    elif isinstance(term, Cons):
        a, n, x, xs = _unpack(term)
        return VCons(evalC(a, env), evalC(n, env),
                     evalC(x, env), evalC(xs, env))
    elif isinstance(term, VecElim):
        a, m, mn, mc, n, xs = _unpack(term)
        mnVal = evalC(mn, env)
        mcVal = evalC(mc, env)
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
        return rec2(evalC(n,env), evalC(xs,env))
    raise TypeError(f"Unknown instance '{type(term)}'")

def vapp(value : Value, v : Value) -> Value:
    check_argument_types()
    if isinstance(value, VLam):
        f, = _unpack(value)
        return f(v)
    elif isinstance(value, VNeutral):
        n, =  _unpack(value)
        return VNeutral(NApp(n, v))
    raise TypeError(f"Unknown instance '{type(v)}'")

def evalC(term : TermC, env : Env) -> Value:
    check_argument_types()
    if isinstance(term, Inf):
        return evalI(term.e, env)
    elif isinstance(term, Lam):
        lam_expr = term.e
        return VLam(lambda x : evalC(lam_expr, [x] + env))
    raise TypeError(f"Unknown instance '{type(term)}'")


def typeI0(c : Context, term : TermI) -> Type:
    check_argument_types()
    return typeI(0, c, term)

def dict_merge(a : TDict[TAny, TAny],
               b : TDict[TAny, TAny]) -> TDict[TAny, TAny]:
    a = a.copy()
    a.update(b)
    return a

def typeI(i : int, c : Context, term : TermI) -> Type:
    check_argument_types()
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
        a, k, x, xs = _unpack(term)
        typeC(i,c, a, VStar())
        aVal = evalC(term.a, [])
        typeC(i,c, k, VNat())
        kVal = evalC(term.n, [])
        typeC(i,c,x, aVal)
        typeC(i,c,xs, VVec(aVal, kVal))
        return VVec(aVal, VSucc(kVal))
    elif isinstance(term, VecElim):
        a,m,mn,mc,k,vs = _unpack(term)
        typeC(i,c,a,VStar())
        aVal = evalC(a, [])
        typeC(i,c,m, VPi(VNat(), lambda k : VPi(VVec(aVal,k),
                                     lambda _ : VStar())))
        mVal = evalC(m, [])
        typeC(i,c,mn, foldl(vapp, mVal, [VZero(), VNil(aVal)]))
        typeC(i,c,mc,
                VPi(VNat(), lambda l:
                    VPi(aVal, lambda y:
                        VPi(VVec(aVal,l), lambda ys:
                            VPi(foldl(vapp, mVal, [l,ys]), lambda _:
                                foldl(vapp, mVal, [VSucc(l), VCons(aVal,l,y,ys)]
                                    ))))))
        typeC(i,c,k,VNat())
        kVal = evalC(k, [])
        typeC(i,c,vs,VVec(aVal,kVal))
        vsVal = evalC(vs, [])
        return fold(vapp, [kVal, vsVal], mVal)
    raise TypeError(f"Unknown instance '{type(term)}'")

def typeC(i : int, c: Context, term : TermC, type_ : Type) -> None:
    check_argument_types()
    if isinstance(term, Inf):
        e, = _unpack(term)
        v = type_
        vp = typeI(i, c, e)
        if quote0(v) != quote0(vp):
            raise TypeError(f"type mismatch: {quote0(v)} != {quote0(vp)}")
        return
    elif isinstance(term, Lam) and isinstance(type_,VPi):
        e, = _unpack(term)
        t, tp = _unpack(type_)
        typeC(i+1, dict_merge({Local(i): t}, c),
                   substC(0, Free(Local(i)), e), tp(vfree(Local(i))))
        return
    raise TypeError(f"Type mismatch: term={type(term)}', type={type(type_)}")

def substI(i : int, r : TermI, t : TermI) -> TermI:
    check_argument_types()
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
    check_argument_types()
    if isinstance(t, Inf):
        return Inf(substI(i,r,t.e))
    elif isinstance(t, Lam):
        return Lam(substC(i+1, r, t.e))
    raise TypeError(f"Unknown instance '{type(t)}'")

def quote0(v : Value) -> TermC:
    check_argument_types()
    return quote(0,v)


def quote(i : int, v : Value) -> TermC:
    check_argument_types()
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
    check_argument_types()
    if isinstance(n, NFree):
        return boundfree(i,n.x)
    elif isinstance(n, NApp):
        return App(neutralQuote(i, n.n), quote(i,n.v))
    elif isinstance(n, NNatElim):
        return NatElim(quote(i,n.a), quote(i,n.n),
                       quote(i,n.x), Inf(neutralQuote(i,n.xs)))
    raise TypeError(f"Unknown instance '{type(n)}'")

def boundfree(i : int, x : Name) -> TermI:
    check_argument_types()
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

plusl : TLam[[TermC], TermI] = lambda x : NatElim(
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

Plus = Ann(Lam(Inf(NatElim(
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
print("type(Plus)=", typeI0({}, Plus))

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

print("2+2 ->", nval2int(evalI(App(App(Plus, int2nat(2)), int2nat(2)),[])))
#sys.exit(0)

## > plus 40 2
## 42 :: Nat
n40 = int2nat(40)
print("n40=", n40)
n2  = int2nat(2)
print("n2=", n2)
print("type(n40)=", typeI0({},_cast(Inf,n40).e))
print("type(plusl(n40))=", typeI0({},plusl(n40)))
n42term = App(plusl(n40),n2)
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
    def __init__(self, func : TUnion[TLam[[TAny],TAny], TLam[[TAny,TAny],TAny]]):
        self.func = func
    def __or__(self, other : TAny) -> TAny:
        return _cast(TLam[[TAny],TAny],self.func)(other)
    def __ror__(self, other : TAny) -> Infix:
        return Infix(partial(self.func, other))

@Infix
def app(x : TermI, y : TermC) -> TermI:
    return App(x,y)

n1 = int2nat(1)
n2a = plusl(n1) |app| n1
print("n2a=", n2a)
print("type(n2a)=", typeI0({}, n2a))
n2e = evalI(n2a, [])
print("n2e=", n2e)
print("n2e=", nval2int(n2e))
n4 = App(plusl(Inf(n2a)), Inf(n2a))
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


def plus(x : TermC, y : TermC) -> TermC:
    return Inf(Plus |app| x |app| y)

def bound(i : int) -> TermC:
    return Inf(Bound(i))
def vec(a : TermC, n : TermC) -> TermC:
    return Inf(Vec(a,n))

Append = Ann(Lam(Lam(Lam(Inf(VecElim(
               bound(2),
               Lam(Lam(pi(Inf(Nat()),
                    pi(vec(bound(5),bound(0)),
                        vec(bound(6), plus(bound(3),bound(1))))))),
               Lam(Lam(bound(0))),
               Lam(Lam(Lam(Lam(Lam(Lam(
                   Inf(Cons(bound(8),
                        plus(bound(5), bound(1)),
                        bound(4),
                        Inf(App(App(Bound(2),bound(1)),bound(0))))))))))),
                   bound(1), bound(0)))))),
        pi(Inf(Star()),
            pi(Inf(Nat()),
                pi(Inf(Vec(bound(1), bound(0))),
                    pi(Inf(Nat()),
                        pi(Inf(Vec(bound(3), bound(0))),
                            Inf(Vec(bound(4), plus(bound(3),bound(1))))))))))

print("Append=", Append)
print("type(Append)=", typeI0({}, Append))


env42 : Context
env42 = {Global("a"):VStar(),
         Global("x"):VNeutral(NFree(Global("a"))),
         Global("y"):VNeutral(NFree(Global("a")))}
e42_v2 = Inf(Cons(free("a"),
          int2nat(1),
          free("x"),
          Inf(Cons(free("a"), int2nat(0), free("x"),
          Inf(Nil(free("a")))))))
e42_v1 = Inf(Cons(free("a"),
          int2nat(0),
          free("y"),
          Inf(Nil(free("a")))))
e42_v3 = Append |app| free("a") \
             |app| int2nat(2) \
             |app| e42_v2 \
             |app| int2nat(1) \
             |app| e42_v1

print("e42_v3=", e42_v3)
print("type(ev42_v3)=", typeI0(env42,e42_v3))
print("eval(ev42_v3)=", evalI(e42_v3, []))




