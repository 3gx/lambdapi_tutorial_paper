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
                   cast as _cast, Iterator as TIter
import sys
from dataclasses import dataclass
import dataclasses as _dc
import typeguard
import functools
from functools import reduce as fold
foldl : TLam[[TAny, TAny, TAny], TAny] = lambda func, acc, xs: functools.reduce(func, xs, acc)

_dc_attrs = {"frozen": True, "repr": False}
class _match_context:
    class _skip(Exception): pass

    def __init__(self, obj : TAny, cls : TAny):
        self.skip = not isinstance(obj, cls)
        self.obj = obj

    def __enter__(self) -> TAny:
        if self.skip:
            import sys
            sys.settrace(lambda *args, **keys: None)
            frame = sys._getframe(1)
            frame.f_trace = self.trace # type: ignore
            return None
        return self.obj

    def trace(self, frame, event, arg): #type: ignore
        raise _match_context._skip()

    def __exit__(self, type, value, traceback): #type: ignore
        if type is None:
            return  # No exception
        if issubclass(type, _match_context._skip):
            return True  # Suppress special SkipWithBlock exception



class Unpack:
    def __iter__(self) -> TIter[TAny]:
        yield from [getattr(self, field.name) for field in _dc.fields(self)]
    def __repr__(self) -> str:
        string = f"{self.__class__.__name__}("
        keys = [field.name for field in _dc.fields(self)]
        for i, k in enumerate(keys):
            value = getattr(self,k)
            if isinstance(value, str):
                string += f"'{value}'"
            else:
                string += f"{value}"
            if i < len(keys)-1:
                string += ","
        string += ")"
        return string
    def classof(self, cls : TAny) -> bool:
        return isinstance(self, cls)

    def match(self, cls : TAny) -> TAny:
        return _match_context(self, cls)



check_types = True
check_types = False
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
class Ann(Unpack):
    e1 : TermC
    e2 : TermC
@dataclass(**_dc_attrs)
class Star(Unpack):
    def __repr__(self) -> str:
        return f"*"
@dataclass(**_dc_attrs)
class Pi(Unpack):
    e1 : TermC
    e2 : TermC
@dataclass(**_dc_attrs)
class Bound(Unpack):
    i : int
    def __repr__(self) -> str:
        return f"(Bound {self.i})"
@dataclass(**_dc_attrs)
class Free(Unpack):
    x : Name
    def __repr__(self) -> str:
        return f"{self.x}"
@dataclass(**_dc_attrs)
class App(Unpack):
    e1:  TermI
    e2 : TermC
@dataclass(**_dc_attrs)
class Nat(Unpack):
    def __repr__(self) -> str:
        return "Nat"
@dataclass(**_dc_attrs)
class NatElim(Unpack):
    e1 : TermC
    e2 : TermC
    e3 : TermC
    e4 : TermC
@dataclass(**_dc_attrs)
class Zero(Unpack):
    def __repr__(self) -> str:
        return "Zero"
@dataclass(**_dc_attrs)
class Succ(Unpack):
    k : TermC
    def __repr__(self) -> str:
        return f"(Succ {self.k})"
@dataclass(**_dc_attrs)
class Vec(Unpack):
    a : TermC
    n : TermC
    def __repr__(self) -> str:
        return f"(Vec {self.a} {self.n})"
@dataclass(**_dc_attrs)
class Nil(Unpack):
    a : TermC
    def __repr__(self) -> str:
        return f"(Nil {self.a})"
@dataclass(**_dc_attrs)
class Cons(Unpack):
    a : TermC
    n : TermC
    x : TermC
    xs : TermC
    def __repr__(self) -> str:
        return f"(Cons {self.a} {self.n} {self.x} {self.xs})"
@dataclass(**_dc_attrs)
class VecElim(Unpack):
    a : TermC
    m : TermC
    mn : TermC
    mc : TermC
    n : TermC
    xs : TermC

TermC = TUnion["Inf", "Lam"]
@dataclass(**_dc_attrs)
class Inf(Unpack):
    e : TermI
    def __repr__(self) -> str:
        return f"{self.e}"
@dataclass(**_dc_attrs)
class Lam(Unpack):
    e : TermC


Name = TUnion["Global", "Local", "Quote"]
@dataclass(**_dc_attrs)
class Global(Unpack):
    str_ : str
    def __repr__(self) -> str:
        return f"'{self.str_}'"
@dataclass(**_dc_attrs)
class Local(Unpack):
    i : int
@dataclass(**_dc_attrs)
class Quote(Unpack):
    i : int

_VFunT0 = TLam[["Value"], "Value"]
_VFunT = TUnion[Box[_VFunT0], _VFunT0]
@dataclass(**_dc_attrs)
class VLam(Unpack):
    f : _VFunT
    def __repr__(self) -> str:
        return f"{quote0(self)}"
@dataclass(**_dc_attrs)
class VNeutral(Unpack):
    n : Neutral
@dataclass(**_dc_attrs)
class VStar(Unpack):
    def __repr__(self) -> str:
        return f"*"
@dataclass(**_dc_attrs)
class VPi(Unpack):
    v : Value
    f : _VFunT
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
    k : Value
    def __repr__(self) -> str:
        return f"{quote0(self)}"
@dataclass(**_dc_attrs)
class VNil(Unpack):
    a : Value
    def __repr__(self) -> str:
        return f"{quote0(self)}"
@dataclass(**_dc_attrs)
class VCons(Unpack):
    a : Value
    n : Value
    x : Value
    xs : Value
    def __repr__(self) -> str:
        return f"{quote0(self)}"
@dataclass(**_dc_attrs)
class VVec(Unpack):
    a : Value
    n : Value
    def __repr__(self) -> str:
        return f"{quote0(self)}"

Value = TUnion[VLam, VNeutral, VStar, VPi, \
               VNat, VZero, VSucc, \
               VNil, VCons, VVec]


Neutral = TUnion["NFree", "NApp", "NNatElim", "NVecElim"]
@dataclass(**_dc_attrs)
class NFree(Unpack):
    x : Name
@dataclass(**_dc_attrs)
class NApp(Unpack):
    n : Neutral
    v : Value
@dataclass(**_dc_attrs)
class NNatElim(Unpack):
    a  : Value
    n  : Value
    x  : Value
    xs : Neutral
@dataclass(**_dc_attrs)
class NVecElim(Unpack):
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
    check_argument_types()
    if term.classof(Ann):
        e, _ = term
        return evalC(e, env)
    if isinstance(term, Free):
        x, = term
        return vfree(x)
    if isinstance(term, Bound):
        i : int
        i, = term
        return env[i]
    if isinstance(term, App):
        e, e1 = term
        return vapp(evalI(e, env), evalC(e1, env))
    if isinstance(term, Star):
        return VStar()
    if isinstance(term, Pi):
        t,t1 = term
        return VPi(evalC(t,env), lambda x: evalC(t1, [x] + env))
    if isinstance(term, Nat):
        return VNat()
    if isinstance(term, Zero):
        return VZero()
    if isinstance(term, Succ):
        k, = term
        return VSucc(evalC(k, env))
    with term.match(NatElim) as (m, mz, ms, k):
        mzVal = evalC(mz, env)
        msVal = evalC(ms, env)
        def rec1(kVal : Value) -> Value:
            #check_argument_types() # fails (yikes)
            if isinstance(kVal, VZero):
                return mzVal
            if isinstance(kVal, VSucc):
                return vapp(vapp(msVal, kVal.k), rec1(kVal.k))
            if isinstance(kVal, VNeutral):
                return VNeutral(NNatElim(evalC(m,env), mzVal, msVal, kVal.n))
            raise TypeError(f"Unknown instance '{type(kVal)}'")
        return rec1(evalC(k, env))
    if isinstance(term, Vec):
        a, n = term
        return VVec(evalC(a, env), evalC(n, env))
    if isinstance(term, Nil):
        a, = term
        return VNil(evalC(a, env))
    if isinstance(term, Cons):
        a, n, x, xs = term
        return VCons(evalC(a, env), evalC(n, env),
                     evalC(x, env), evalC(xs, env))
    if isinstance(term, VecElim):
        a, m, mn, mc, n, xs = term
        mnVal = evalC(mn, env)
        mcVal = evalC(mc, env)
        def rec2(nVal : Value, xsVal : Value) -> Value:
            if isinstance(xsVal, VNil):
                return mnVal
            if isinstance(xsVal, VCons):
                l,x,xs = (xsVal.n, xsVal.x, xsVal.xs)
                return fold(vapp, [l,x,xs,rec2(l,xs)], mcVal)
            if isinstance(xsVal, VNeutral):
                return VNeutral(NVecElim(evalC(a, env),
                                         evalC(m, env),
                                         mnVal, mcVal, nVal, xsVal.n))
            raise TypeError(f"Unknown instance '{type(xsVal)}'")
        return rec2(evalC(n,env), evalC(xs,env))
    raise TypeError(f"Unknown instance '{type(term)}'")

def vapp(value : Value, v : Value) -> Value:
    check_argument_types()
    if isinstance(value, VLam):
        f, = value
        return f(v)
    elif isinstance(value, VNeutral):
        n, =  value
        return VNeutral(NApp(n, v))
    raise TypeError(f"Unknown instance '{type(v)}'")

def evalC(term : TermC, env : Env) -> Value:
    check_argument_types()
    if isinstance(term, Inf):
        e, = term
        return evalI(e, env)
    elif isinstance(term, Lam):
        lam_expr, = term
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
        e1, e2 = term
        typeC(i, c, e2, VStar())
        t = evalC(e2, [])
        typeC(i, c, e1, t)
        return t
    elif isinstance(term, Free):
        x, = term
        return c[x]
    elif isinstance(term, App):
        e1, e2 = term
        s = typeI(i, c, e1)
        if isinstance(s, VPi):
            typeC(i, c, e2, s.v)
            return s.f(evalC(e2, []))
    elif isinstance(term, Star):
        return VStar()
    elif isinstance(term, Pi):
        p, p1 = term
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
        m, mz, ms, k = term
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
        a, n = term
        typeC(i,c,a, VStar())
        typeC(i,c,n, VNat())
        return VStar()
    elif isinstance(term, Nil):
        a, = term
        typeC(i,c,a, VStar())
        aVal = evalC(a, [])
        return VVec(aVal, VZero())
    elif isinstance(term, Cons):
        a, k, x, xs = term
        typeC(i,c, a, VStar())
        aVal = evalC(a, [])
        typeC(i,c, k, VNat())
        kVal = evalC(k, [])
        typeC(i,c,x, aVal)
        typeC(i,c,xs, VVec(aVal, kVal))
        return VVec(aVal, VSucc(kVal))
    elif isinstance(term, VecElim):
        a,m,mn,mc,k,vs = term
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
        e, = term
        v = type_
        vp = typeI(i, c, e)
        if quote0(v) != quote0(vp):
            raise TypeError(f"type mismatch: {quote0(v)} != {quote0(vp)}")
        return
    elif isinstance(term, Lam) and isinstance(type_,VPi):
        e, = term
        t, tp = type_
        typeC(i+1, dict_merge({Local(i): t}, c),
                   substC(0, Free(Local(i)), e), tp(vfree(Local(i))))
        return
    raise TypeError(f"Type mismatch: term={type(term)}', type={type(type_)}")

def substI(i : int, r : TermI, t : TermI) -> TermI:
    check_argument_types()
    if isinstance(t, Ann):
        e1,e2 = t
        return Ann(substC(i,r,e1), e2)
    elif isinstance(t, Bound):
        j, = t
        return r if i == j else Bound(j)
    elif isinstance(t, Free):
        return t
    elif isinstance(t, App):
        e1,e2 = t
        return App(substI(i,r,e1), substC(i,r,e2))
    elif isinstance(t, Star):
        return Star()
    elif isinstance(t, Pi):
        f, v = t
        return Pi(substC(i,r,f), substC(i+1, r, v))
    elif isinstance(t, Nat):
        return Nat()
    elif isinstance(t, Zero):
        return Zero()
    elif isinstance(t, Succ):
        k, = t
        return Succ(substC(i,r,k))
    elif isinstance(t, NatElim):
        m, mz, ms, k = t
        return NatElim(substC(i,r,m),
                       substC(i,r,mz),
                       substC(i,r,ms),
                       substC(i,r,k))
    elif isinstance(t, Vec):
        a,n = t
        return Vec(substC(i,r,a), substC(i,r,n))
    elif isinstance(t, Nil):
        a, = t
        return Nil(substC(i,r,a))
    elif isinstance(t, Cons):
        a,n,x,xs = t
        return Cons(substC(i,r,a), substC(i,r,n),
                    substC(i,r,x), substC(i,r,xs))
    elif isinstance(t,VecElim):
        a,m,mn,mc,n,xs = t
        return VecElim(substC(i,r,a), substC(i,r,m),
                       substC(i,r,mn), substC(i,r,mc),
                       substC(i,r,n), substC(i,r,xs))
    raise TypeError(f"Unknown instance '{type(t)}'")

def substC(i : int, r : TermI, t : TermC) -> TermC:
    check_argument_types()
    if isinstance(t, Inf):
        e, = t
        return Inf(substI(i,r,e))
    elif isinstance(t, Lam):
        e, = t
        return Lam(substC(i+1, r, e))
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



import time
t1 = time.time()
for i in range(1000):
    evalI(e42_v3,[])
t2 = time.time()
print(t2-t1)


