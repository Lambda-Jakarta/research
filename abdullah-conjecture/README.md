The Haskell source file [AbdullahConjecture.hs](AbdullahConjecture.hs)
is a manual translation of the Lean source file [abdullah.lean](abdullah.lean).

The statement of the Abdullah conjecture follows.
(I (Erik) might have misunderstood it. We should ask Abdullah.)

For every Haskell type endofunction `f :: * -> *`,
we can construct functions `hom1` and `hom2` having these types:

```
hom1 :: (forall m. (Monad m) => f (m a)) -> (forall r. f (Cont r a))
hom2 :: (forall r. f (Cont r a)) -> (forall m. (Monad m) => f (m a))
```
