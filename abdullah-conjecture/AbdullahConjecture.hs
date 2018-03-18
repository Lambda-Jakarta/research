{-# LANGUAGE RankNTypes #-}

module AbdullahConjecture where

{-
2018-01-04
2018-01-12
Erik Dominikus
-}

-- Cont used to be a newtype.
type Cont r a = (a -> r) -> r

mkCont :: ((a -> r) -> r) -> Cont r a
mkCont = id

unCont :: Cont r a -> ((a -> r) -> r)
unCont = id

{-
All the ways to build a rank-1 (Haskell-98) type endofunction.
Every newtype here corresponds to a constructor in the `endo` inductive data type in the Lean source file.
Every rank-1 type endofunction can be built by repeatedly composing these five type endofunctions (modulo newtypes).

Examples:
\ t -> c                        Con c
\ t -> t                        Var
\ t -> a t -> b t               Arr a b
\ t -> (a t, b t)               Prod a b
\ t -> Either (a t) (b t)       Sum a b
\ t -> (t, t)                   Prod Var Var
\ t -> (t -> t) -> t            Arr (Arr Var Var) Var
\ t -> t -> (t -> t)            Arr Var (Arr Var Var)

The schema is defined by the `render` function in the Lean source file.
That is:

definition render : endo → (Type → Type)
| (@endo.con c _) := λ t, c
| (endo.var) := λ t, t
| (endo.arr a b) := λ t, render a t → render b t
| (endo.prod a b) := λ t, render a t × render b t
| (endo.sum a b) := λ t, render a t ⊕ render b t
-}

newtype Con c t = MkCon { unCon :: c }
newtype Var t = MkVar { unVar :: t }
newtype Arr a b t = MkArr { unArr :: a t -> b t }
newtype Prod a b t = MkProd { unProd :: (a t, b t) }
newtype Sum a b t = MkSum { unSum :: Either (a t) (b t) }

prodMap :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
prodMap f g (x, y) = (f x, g y)

sumMap :: (a -> c) -> (b -> d) -> Either a b -> Either c d
sumMap f g (Left x) = Left (f x)
sumMap f g (Right x) = Right (g x)

-- These correspond to `lem_render_m_to_cont` and `lem_render_cont_to_m` in the Lean source file.
-- These two lemmas are needed to prove `hom_2`.
class MToCont f where mToCont :: (Monad m) => f (m t) -> f (Cont (m t) t)
class ContToM f where contToM :: (Monad m) => f (Cont (m t) t) -> f (m t)

instance MToCont (Con c) where mToCont i = MkCon (unCon i)
instance MToCont Var where mToCont i = MkVar (mkCont (\ c -> unVar i))
instance (ContToM u, MToCont v) => MToCont (Arr u v) where mToCont ra = MkArr (\ ru -> mToCont (unArr ra (contToM ru)))
instance (MToCont u, MToCont v) => MToCont (Prod u v) where mToCont ra = MkProd (prodMap mToCont mToCont (unProd ra))
instance (MToCont u, MToCont v) => MToCont (Sum u v) where mToCont ra = MkSum (sumMap mToCont mToCont (unSum ra))

instance ContToM (Con c) where contToM i = MkCon (unCon i)
instance ContToM Var where contToM ra = MkVar (unCont (unVar ra) pure)
instance (MToCont u, ContToM v) => ContToM (Arr u v) where contToM ra = MkArr (\ ru -> contToM (unArr ra (mToCont ru)))
instance (ContToM u, ContToM v) => ContToM (Prod u v) where contToM ra = MkProd (prodMap contToM contToM (unProd ra))
instance (ContToM u, ContToM v) => ContToM (Sum u v) where contToM ra = MkSum (sumMap contToM contToM (unSum ra))

-- This corresponds to theorem `hom_2` in the Lean source file.
class Hom2 f where hom2 :: (forall r. f (Cont r a)) -> (forall m. (Monad m) => f (m a))
instance Hom2 (Con c) where hom2 x = MkCon (unCon x)
instance Hom2 Var where hom2 h = MkVar (unCont (unVar h) pure)
instance (MToCont u, ContToM v) => Hom2 (Arr u v) where hom2 h = MkArr (\ ru -> contToM (unArr h (mToCont ru)))
instance (ContToM u, ContToM v) => Hom2 (Prod u v) where hom2 h = MkProd (prodMap contToM contToM (unProd h))
instance (ContToM u, ContToM v) => Hom2 (Sum u v) where hom2 h = MkSum (sumMap contToM contToM (unSum h))

-- Therefore, Hom2 holds for every rank-1 (Haskell-98) type endofunction (modulo newtypes).


-- This is not needed for proving `hom_2`.
-- This corresponds to the `conjure` lemma in the Lean source file.
class Inhabited a where def :: a
class Conjure f where conjure :: a -> f a
instance (Inhabited c) => Conjure (Con c) where conjure _ = MkCon def
instance Conjure Var where conjure x = MkVar x
instance (Conjure v) => Conjure (Arr u v) where conjure xt = MkArr (\ _ -> conjure xt)
instance (Conjure u, Conjure v) => Conjure (Prod u v) where conjure xt = MkProd (conjure xt, conjure xt)
instance (Conjure v) => Conjure (Sum u v) where conjure xt = MkSum (Right (conjure xt))
-- instance (Conjure u) => Conjure (Sum u v) where conjure xt = MkSum (Left (conjure xt)) -- another possible instance


-- This `main` is so that https://repl.it/languages/haskell doesn't complain.

main :: IO ()
main = return ()
