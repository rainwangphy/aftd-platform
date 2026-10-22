import AFTD.Prelude
import AFTD.Kb.Optimization.KSubmodMeet
import AFTD.Kb.Optimization.KSubmodJoin

/-!
# is_k_submodular

Topic: submodular   Node: a59f7e507566

Provenance: formalization of a published result. Source: arXiv:2610.26677, Eq. (1)

A function f : (Fin n → Option (Fin k)) → ℝ is k-submodular if for all x and y, f (x ⊓ y) + f (x ⊔ y) ≤ f x + f y.
-/

/-- Predicate asserting that a function on assignments is k-submodular. -/
def is_k_submodular {n k : ℕ} (f : (Fin n → Option (Fin k)) → ℝ) : Prop := ∀ x y, f (k_submod_meet x y) + f (k_submod_join x y) ≤ f x + f y
