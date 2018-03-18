-- 2018-01-04
-- Erik Dominikus

-- These are the definitions required to state the things we want to prove.

definition Cont (r : Type) (a : Type) : Type := (a → r) → r

structure Functor (m : Type → Type) : Type 1 := mk ::
    (map : Π {a b}, (a → b) → m a → m b)
    (pure : Π {a}, a → m a)
    (p0 : Π {a}, @map a a id = id)
    (p1 : Π {a b c} (f : b → c) (g : a → b), map (f ∘ g) = map f ∘ map g)
    (p2 : Π {a b} (f : a → b) x, map f (pure x) = pure (f x))

structure Monad (m : Type → Type) : Type 1 := mk ::
    (functor : Functor m)
    (join : Π {a}, m (m a) → m a)

definition Monad.pure : Π {m a}, Monad m → (a → m a) := λ _ _ mi, Functor.pure (Monad.functor mi)

definition instance_Functor_Cont (r) : Functor (λ a, Cont r a) := {
    map := λ a b (f : a → b) (ma : (a → r) → r), λ (c : b → r), begin
        let d : a → r := λ x, c (f x),
        exact ma d
    end,
    pure := λ _ x, λ c, c x,
    p0 := begin intros, refl end,
    p1 := begin intros, refl end,
    p2 := begin intros, simp end,
}

definition instance_Monad_Cont : Π {r}, Monad (Cont r) := λ r, {
    functor := instance_Functor_Cont r,
    join := λ a (m : (((a → r) → r) → r) → r), begin
        intro c0,
        let d0 : ((a → r) → r) → r := λ c1, c1 c0,
        exact m d0
    end,
}

definition sum.map_both {a b c d} (f : a → c) (g : b → d) (s : a ⊕ b) : c ⊕ d := match s with
| sum.inl x := sum.inl (f x)
| sum.inr x := sum.inr (g x)
end

-- Hom_1 and Hom_2 are the statements we want to prove.

definition Hom_1 (f : Type → Type) := Π {a : Type}, (Π {m}, Monad m → f (m a)) → (Π {r : Type}, f (Cont r a))
definition Hom_2 (f : Type → Type) := Π {a : Type}, (Π {r : Type}, f (Cont r a)) → (Π {m}, Monad m → f (m a))

-- This is a proof of Hom_1.

theorem hom_1_trivial (f : Type → Type) : Hom_1 f :=
begin
    intros a hm r,
    let m := Cont r,
    let j := hm instance_Monad_Cont,
    exact j
end

-- Here we tell Lean how to construct a Haskell 98 type endofunction.

-- This describes all the possible ways to construct a rank-1 (Haskell 98) type endofunction.
-- See `render` for what this represents.
inductive endo
| con : Π {t : Type}, t → endo -- c, and proof of inhabitedness
| var : endo -- a (the only type variable in a rank-1 type endofunction body)
| arr : endo → endo → endo
| prod : endo → endo → endo
| sum : endo → endo → endo

-- `render e` is the type endofunction represented by `e`.
definition render : endo → (Type → Type)
| (@endo.con c _) := λ t, c
| (endo.var) := λ t, t
| (endo.arr a b) := λ t, render a t → render b t
| (endo.prod a b) := λ t, render a t × render b t
| (endo.sum a b) := λ t, render a t ⊕ render b t

-- This is used in the theorem `hom_2`.
-- `lem_render_m_to_cont` enables us to transform `m t` to `Cont (m t) t`.
-- `lem_render_cont_to_m` enables us to transform `Cont (m t)` t to `m t`.
mutual lemma lem_render_m_to_cont, lem_render_cont_to_m with
lem_render_m_to_cont : Π (a : endo) (m : Type → Type) (mi : Monad m) t (ra : render a (m t)), render a (Cont (m t) t)
| (@endo.con c i) := begin intros, exact i end
| (endo.var) := begin intros, intros c, exact ra end
| (endo.arr u v) := begin intros,
    let ra0 : render u (m t) → render v (m t) := ra,
    have goal : render u (Cont (m t) t) → render v (Cont (m t) t) := begin
        intros ru,
        apply lem_render_m_to_cont v m mi t,
        apply ra0,
        apply lem_render_cont_to_m u m mi t,
        exact ru
    end,
    exact goal
end
| (endo.prod u v) := begin intros,
    apply @prod.map (render u (m t)) (render u (Cont (m t) t)) (render v (m t)) (render v (Cont (m t) t)),
    apply lem_render_m_to_cont u m mi t,
    apply lem_render_m_to_cont v m mi t,
    exact ra
end
| (endo.sum u v) := begin intros,
    apply @sum.map_both (render u (m t)) (render v (m t)) (render u (Cont (m t) t)) (render v (Cont (m t) t)),
    apply lem_render_m_to_cont u m mi t,
    apply lem_render_m_to_cont v m mi t,
    exact ra
end
with lem_render_cont_to_m : Π a (m : Type → Type) (mi : Monad m) t (ra : render a (Cont (m t) t)), render a (m t)
| (@endo.con c i) := begin intros, exact i end
| (endo.var) := begin intros, exact ra (Monad.pure mi) end
| (endo.arr u v) := begin intros,
    let ra0 : render u (Cont (m t) t) → render v (Cont (m t) t) := ra,
    have goal : render u (m t) → render v (m t) := begin
        intros ru,
        apply lem_render_cont_to_m v m mi t,
        apply ra0,
        apply lem_render_m_to_cont u m mi t,
        exact ru
    end,
    exact goal
end
| (endo.prod u v) := begin intros,
    apply @prod.map (render u (Cont (m t) t)) (render u (m t)) (render v (Cont (m t) t)) (render v (m t)),
    apply lem_render_cont_to_m u m mi t,
    apply lem_render_cont_to_m v m mi t,
    exact ra
end
| (endo.sum u v) := begin intros,
    apply @sum.map_both (render u (Cont (m t) t)) (render v (Cont (m t) t)) (render u (m t)) (render v (m t)),
    apply lem_render_cont_to_m u m mi t,
    apply lem_render_cont_to_m v m mi t,
    exact ra
end

-- This is the proposed proof of the non-trivial part of Abdullah conjecture for all Haskell 98 type endofunctions.

theorem hom_2 : Π (e : endo), Hom_2 (render e)
| (@endo.con c i) := begin intros t h m mi, exact i end
| (endo.var) := begin intros t h m mi, exact @h (m t) (Monad.pure mi) end
| (endo.arr u v) := begin intros t h m mi,
    have goal : render u (m t) → render v (m t) := begin
        intros ru,
        apply lem_render_cont_to_m v m mi t,
        let hh : render u (Cont (m t) t) → render v (Cont (m t) t) := @h (m t),
        apply hh,
        apply lem_render_m_to_cont u m mi t,
        exact ru
    end,
    exact goal
end
| (endo.prod u v) := begin intros t h m mi,
    apply @prod.map (render u (Cont (m t) t)) (render u (m t)) (render v (Cont (m t) t)) (render v (m t)),
    exact lem_render_cont_to_m u m mi t,
    exact lem_render_cont_to_m v m mi t,
    exact @h (m t)
end
| (endo.sum u v) := begin intros t h m mi,
    apply @sum.map_both (render u (Cont (m t) t)) (render v (Cont (m t) t)) (render u (m t)) (render v (m t)),
    exact lem_render_cont_to_m u m mi t,
    exact lem_render_cont_to_m v m mi t,
    exact @h (m t)
end
