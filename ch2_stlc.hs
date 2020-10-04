import Control.Monad (unless)

data TermI = Ann TermC Type
           | Bound Int
           | Free Name
           | TermI :@: TermC
       deriving (Show,Eq)

data TermC = Inf TermI
           | Lam TermC
         deriving (Show, Eq)

data Name = Global String
          | Local Int
          | Quote Int
       deriving (Show, Eq)

data Type = TFree Name
          | Fun Type Type
       deriving (Show, Eq)

data Value = VLam (Value -> Value)
           | VNeutral Neutral

data Neutral = NFree Name
             | NApp Neutral Value

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

type Env = [Value]

evalI :: TermI -> Env -> Value
evalI (Ann e _) d = evalC e d
evalI (Free x)  d = vfree x
evalI (Bound i) d = d !! i
evalI (e :@: e') d = vapp (evalI e d) (evalC e' d)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

evalC :: TermC -> Env -> Value
evalC (Inf i) d = evalI i d
evalC (Lam e) d = VLam (\x -> evalC e (x:d))

data Kind = Star
        deriving (Show)

data Info = HasKind Kind
          | HasType Type
       deriving (Show)

type Context =[(Name, Info)]

type Result a = Either String a

throwError :: String -> Result a
throwError str = Left str

kindC :: Context -> Type -> Kind -> Result ()
kindC context (TFree x) Star
  = case lookup x context of
      Just (HasKind start) -> return ()
      Nothing              -> throwError "unknown var identifier"

kindC context (Fun k k') Star
  = do kindC context k Star
       kindC context k' Star

typeI0 :: Context -> TermI -> Result Type
typeI0 = typeI 0

typeI :: Int -> Context -> TermI -> Result Type
typeI i context (Ann e t)
  = do kindC context t Star
       typeC i context e t
       return t
typeI i context (Free x)
  = case lookup x context of
       Just (HasType t) -> return t
       Nothing          -> throwError "unknown type identifier"

typeI i context (e :@: e')
  = do s <- typeI i context e
       case s of
          Fun t t' -> do typeC i context e' t
                         return t'
          _ -> throwError "illegal application"

typeC :: Int -> Context -> TermC -> Type -> Result ()
typeC i context (Inf e) t
  = do t' <- typeI i context e
       unless (t == t') (throwError "[inf] type mismatch")

typeC i context (Lam e) (Fun t t')
  = typeC (i+1) ((Local i, HasType t) : context)
                (substC 0 (Free (Local i)) e) t'
typeC i context _ _
  = throwError "oops type mismatch"

substI :: Int -> TermI -> TermI -> TermI
substI i r (Ann e t) = Ann (substC i r e) t
substI i r (Bound j) = if i==j then r else Bound j
substI i r (Free y) = Free y
substI i r (e :@: e') = substI i r e :@: substC i r e'

substC :: Int -> TermI -> TermC -> TermC
substC i r (Inf e) = Inf (substI i r e)
substC i r (Lam e) = Lam (substC (i+1) r e)

quote0 :: Value -> TermC
quote0 = quote 0

quote :: Int -> Value -> TermC
quote i (VLam f) = Lam (quote (i+1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)

neutralQuote :: Int -> Neutral -> TermI
neutralQuote i (NFree x) = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> TermI
boundfree i (Quote k) = Bound (i - k - 1)
boundfree i x = Free x

-- examples

e0 = quote0 (VLam (\x -> VLam (\y -> x)))
-- > e0
-- > Lam (Lam (Inf (Bound 1)))

id' = Lam (Inf (Bound 0))
const' = Lam (Lam (Inf (Bound 1)))
tfree a = TFree (Global a)
free x = Inf (Free (Global x))
term1 = Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y"
term2 = Ann const' (Fun (Fun  (tfree "b") (tfree "b"))
                   (Fun (tfree "a")
                        (Fun (tfree "b") (tfree "b"))))
        :@: id' :@: free "y"
env1 = [(Global "y", HasType (tfree "a")),
        (Global "a", HasKind Star)]
env2 = [(Global "b", HasKind Star)] ++ env1

e1 = quote0 (evalI term1 [])
-- > e1
-- Inf (Free (Global "y"))

e2 = quote0 (evalI term2 [])
-- > e2
-- > Lam (Inf (Bound 0))

e3 = typeI0 env1 term1
-- > e3
-- > Right (TFree (Global "a"))

e4 = typeI0 env2 term2
-- > e4
-- > Right (Fun (TFree (Global "b")) (TFree (Global "b")))



