import AFTD.Prelude

/-!
# not_injOn_of_exists_ne

Topic: combinatorics   Node: 5df74f4e08bd

Provenance: helper lemma. folklore

A function $f$ is not injective on a set $s$ if there exist distinct elements $x, y \in s$ such that $f(x) = f(y)$.
-/

/-- A function is not injective on a set if two distinct elements in the set have the same image. -/
lemma not_injOn_of_exists_ne {α β : Type*} (f : α → β) (s : Set α)
    (x y : α) (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) (hfeq : f x = f y) :
    ¬ Set.InjOn f s := fun hinj => hne (hinj hx hy hfeq)
