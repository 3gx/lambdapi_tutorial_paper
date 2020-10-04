import Control.Monad (unless)


data TermI = Ann TermC TermC
           | Star
           | Pi TermC TermC
           | Bound Int
           | Free Name
           | TermI :@: TermC
           | Nat
           | NatElim TermC TermC TermC TermC
           | Zero
           | Succ TermC
       deriving (Show,Eq)

data TermC = Inf TermI
           | Lam TermC
         deriving (Show, Eq)

data Name = Global String
          | Local Int
          | Quote Int
       deriving (Show, Eq)

data Value = VLam (Value -> Value)
           | VStar
           | VPi Value (Value -> Value)
           | VNeutral Neutral
           | VNat
           | VZero
           | VSucc Value

instance Show Value where
  show x = show (quote0 x)

data Neutral = NFree Name
             | NApp Neutral Value
             | NNatElim Value Value Value Neutral
        deriving Show


type Type = Value

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

type Env = [Value]
type Context = [(Name,Type)]

evalI :: TermI -> Env -> Value

evalI (Ann e _) d = evalC e d
evalI Star d = VStar
evalI (Pi t t') d = VPi (evalC t d) (\x -> evalC t' (x : d))
evalI (Free x)  d = vfree x
evalI (Bound i) d = d !! i
evalI (e :@: e') d = vapp (evalI e d) (evalC e' d)
evalI Nat d = VNat
evalI Zero d = VZero
evalI (Succ k) d = VSucc (evalC k d)
evalI (NatElim m mz ms k) d
  = let mzVal = evalC mz d
        msVal = evalC ms d
        rec kVal =
          case kVal of
            VZero -> mzVal
            VSucc l -> msVal `vapp` l `vapp` rec l
            VNeutral k -> VNeutral
                          (NNatElim (evalC m d) mzVal msVal k)
            _ -> error "internal: eval natElim"
    in rec (evalC k d)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

evalC :: TermC -> Env -> Value
evalC (Inf i) d = evalI i d
evalC (Lam e) d = VLam (\x -> evalC e (x:d))


type Result a = Either String a

throwError :: String -> Result a
throwError str = Left str


typeI0 :: Context -> TermI -> Result Type
typeI0 = typeI 0


typeI :: Int -> Context -> TermI -> Result Type
typeI i context (Ann e p)
  = do typeC i context p VStar
       let t = evalC p []
       typeC i context e t
       return t
typeI i context Star
  = return VStar
typeI i context (Pi p p')
  = do typeC i context p VStar
       let t = evalC p []
       typeC (i+1) ((Local i, t) : context)
             (substC 0 (Free (Local i)) p') VStar
       return VStar
typeI i context (Free x)
  = case lookup x context of
       Just t -> return t
       Nothing -> throwError "unknown type identifier"
typeI i context (e :@: e')
  = do s <- typeI i context e
       case s of
          VPi t t' -> do typeC i context e' t
                         return (t' (evalC e' []))
          _ -> throwError "illegal application"
typeI i context Nat = return VStar
typeI i context Zero = return VNat
typeI i context (Succ k) =
  do typeC i context k VNat
     return VNat
typeI i context (NatElim m mz ms k) =
  do typeC i context m (VPi VNat (const VStar))
     let mVal = evalC m []
     typeC i context mz (mVal `vapp` VZero)
     typeC i context ms (VPi VNat (\l -> VPi (mVal `vapp` l)
                                             (\_ -> mVal `vapp` VSucc l)))
     typeC i context k VNat
     let kVal = evalC k []
     return (mVal `vapp` kVal)


typeC :: Int -> Context -> TermC -> Type -> Result ()
typeC i context (Inf e) v
  = do v' <- typeI i context e
       unless (quote0 v == quote0 v') (throwError "[inf] type mismatch")
typeC i context (Lam e) (VPi t t')
  = typeC (i+1) ((Local i, t) : context)
                (substC 0 (Free (Local i)) e) (t' (vfree (Local i)))
typeC i context _ _
  = throwError "oops .. type mismatch"

substI :: Int -> TermI -> TermI -> TermI
substI i r (Ann e t) = Ann (substC i r e) t
substI i r Star = Star
substI i r (Pi t t') = Pi (substC i r t) (substC (i+1) r t')
substI i r (Bound j) = if i==j then r else Bound j
substI i r (Free y) = Free y
substI i r (e :@: e') = substI i r e :@: substC i r e'
substI i r Nat = Nat
substI i r (NatElim m mz ms n)
  = NatElim (substC i r m)
            (substC i r mz)
            (substC i r ms)
            (substC i r n)
substI i r Zero = Zero
substI i r (Succ n) = Succ (substC i r n)

substC :: Int -> TermI -> TermC -> TermC
substC i r (Inf e) = Inf (substI i r e)
substC i r (Lam e) = Lam (substC (i+1) r e)

quote0 :: Value -> TermC
quote0 = quote 0

quote :: Int -> Value -> TermC
quote i (VLam f) = Lam (quote (i+1) (f (vfree (Quote i))))
quote i VStar = Inf Star
quote i (VPi v f)
  = Inf (Pi (quote i v) (quote (i+1) (f (vfree (Quote i)))))
quote i (VNeutral n) = Inf (neutralQuote i n)
quote i VNat = Inf Nat
quote i VZero = Inf Zero
quote i (VSucc v) = Inf $ Succ (quote i v)

neutralQuote :: Int -> Neutral -> TermI
neutralQuote i (NFree x) = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> TermI
boundfree i (Quote k) = Bound (i - k - 1)
boundfree i x = Free x

-- examples

-- \x -> \y -> x
e0 = quote0 (VLam (\x -> VLam (\y -> x)))
-- > e0
-- > Lam (Lam (Inf (Bound 1)))

id' = Lam (Inf (Bound 0))
const' = Lam (Lam (Inf (Bound 1)))
free x = Inf (Free (Global x))
pi' x y = Inf (Pi x y)
star = Inf Star
ann x y = Inf (Ann x y)
term1 = (Ann id' (Inf (Pi (free "a") (free "a"))) ) :@: (free "y")
term2 = ((Ann const' (pi' (pi' (free "b") (free "b"))
                         (pi' (free "a")
                           (pi' (free "b") (free "b")))))
        :@: id') :@: (free "y")
term2' = ((Ann const' (pi' (pi' (free "b") (free "b"))
                         (pi' (free "a")
                           (pi' (free "b") (free "b")))))
        :@: (free "y")) :@: id'
env1 = [(Global "y", VNeutral (NFree (Global "a"))),
        (Global "a", VStar)]
env2 = [(Global "b", VStar)] ++ env1

--quoteT :: Result Type -> Result Value
--quoteT (Right x) = return (evalI x [])
--quoteT (Left x) = Left x

e1 = quote0 (evalI term1 [])
-- > e1
-- Inf (Free (Global "y")) 

e2 = quote0 (evalI term2 [])
-- > e2
-- Lam (Inf (Bound 0))
--
e2' = quote0 (evalI term2' [])
-- > e2'
-- Int (Free (Global "y"))

e3 = typeI0 env1 term1
-- > e3
-- Right Inf (Free (Global "a"))

e4 = typeI0 env2 term2
-- > e4
-- Right Inf (Pi (Inf (Free (Global "b"))) (Inf (Free (Global "b"))))

-- \x -> \y -> y x
e5 = quote0 (VLam $ \x->
              (VLam $ \y ->
                (VNeutral
                  (NApp
                    (NFree (Global "y"))
                    (VNeutral $ NFree (Global "x")
                    )
                  )
                )
              )
            )
-- > e5
-- Lam (Lam (Inf (Free (Global "y") :@: Inf (Free (Global "x")))))

e6 = Lam (Lam (Inf ((Bound 0) :@: (Inf (Bound 1)))))
-- > e6
-- Lam (Lam (Inf (Bound 0 :@: Inf (Bound 1))))

-- example for the following concrete syntax
-- > let id = (\a x -> x) :: Pi (a :: *).a -> a
-- id :: Pi (x::*) (y::x).x
e35 = (Ann
        (Lam
          (Lam $ Inf (Bound 0))
        )
        (pi'
          (Inf Star)
          (pi'
            (Inf (Bound 0))
            (Inf (Bound 1))
          )
        )
      )

-- > assume (Bool :: *) (False :: Bool)
env35 :: Context
env35 = [(Global "Bool", VStar),
         (Global "False", VNeutral (NFree (Global "Bool")))]
-- > typeI0 env35 e35
-- Right Inf (Pi (Inf Star) (Inf (Pi (Inf (Bound 0)) (Inf (Bound 1)))))

-- > id Bool
-- \x -> x :: Pi x :: Bool. Bool
apply35a = e35 :@: (free "Bool")
-- > typeI0 env35 apply35a
-- Right Inf (Pi (Inf (Free (Global "Bool"))) (Inf (Free (Global "Bool"))))

-- > id Bool False
-- False :: Bool
apply35b = apply35a :@: (free "False")
-- > typeI0 env35 apply35b
-- Right Inf (Free (Global "Bool"))


-- > evalI apply35a []
-- Lam (Inf (Bound 0))
-- > evalI apply35b []
-- Inf (Free (Global "False"))
-- > typeI0 env35 $ Free (Global "False")
-- Right Inf (Free (Global "Bool"))
-- > typeI0 env35 $ Free (Global "Bool")
-- Right Inf Star

-- below is example for the following concrete syntax
-- ==================================================
-- > let plus = natElim (\_ -> Nat -> Nat)
--                      (\n -> n)
--                      (\k rec n -> Succ (rec n))
-- plus :: Pi (x :: Nat) (y :: Nat) . Nat

plus = NatElim
        (Lam (pi' (Inf Nat) (Inf Nat)))
        (Lam (Inf (Bound 0)))
        (Lam
          (Lam
            (Lam
              (Inf
                (Succ (Inf ((Bound 1) :@: (Inf (Bound 0)))))
              )
            )
          )
        )

int2nat :: Int -> TermC
int2nat 0 = Inf Zero
int2nat n = Inf (Succ (int2nat (n-1)))

nval2int :: Value -> Int
nval2int VZero = 0
nval2int (VSucc n) = 1 + (nval2int n)

-- > plus 40 2
-- 42 :: Nat
n40 = int2nat 40
n2  = int2nat 2
n42 = nval2int (evalI (plus n40 :@: n2) [])
-- > n42
-- 42

plus2 = plus (Inf (Succ (Inf (Succ (Inf Zero)))))
three = plus2 :@: (Inf (Succ (Inf Zero)))
five = plus2 :@: (Inf three)
-- > evalI three []
-- Inf (Succ (Inf (Succ (Inf (Succ (Inf Zero))))))
-- > typeI0 [] three
-- Right Inf Nat
-- > evalI five []
-- Inf (Succ (Inf (Succ (Inf (Succ (Inf (Succ (Inf (Succ (Inf Zero))))))))))
-- > typeI0 [] five
-- Right Inf Nat
plus5 = plus (Inf five)
eight = plus5 :@: (Inf three)
-- > evalI eight []
-- Inf (Succ (Inf (Succ (Inf (Succ (Inf (Succ (Inf (Succ (Inf (Succ (Inf (Succ (Inf (Succ (Inf Zero))))))))))))))))
-- > typeI0 [] eight
-- Right Inf Nat

-- proof: 1+1 = 2
one = (Succ (Inf Zero))
two = plus (Inf one) :@: (Inf one)
-- > evalI two []
-- Inf (Succ (Inf (Succ (Inf Zero))))
-- > typeI0 [] two
-- Right Inf Nat

-- proof : 2+2 = 4
four = plus (Inf two) :@: (Inf two)
-- > evalI four []
-- Inf (Succ (Inf (Succ (Inf (Succ (Inf (Succ (Inf Zero))))))))
-- > typeI0 [] four
-- Right Inf Nat

