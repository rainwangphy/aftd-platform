import AFTD.Prelude

/-!
# is_submodular_bounded

Topic: submodular   Node: 66dd5cc05d07

Provenance: formalization of a published result. Source: arXiv:2611.02374 Def. 2.1

A function f on {0, 1}^n with range {0, 1, ..., k} is submodular if f(x ⊔ y) + f(x ⊓ y) ≤ f(x) + f(y) for all x and y.
-/

/-- Submodularity for functions from the n-dimensional hypercube to Fin (k + 1). -/
def is_submodular_bounded (n k : ℕ) (f : (Fin n → Bool) → Fin (k + 1)) : Prop :=
  ∀ x y : Fin n → Bool, (f (x ⊔ y) : ℝ) + (f (x ⊓ y) : ℝ) ≤ (f x : ℝ) + (f y : ℝ)
