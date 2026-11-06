import AFTD.Prelude
import AFTD.Kb.Optimization.CubeFunc

/-!
# is_submodular_cube

Topic: submodular   Node: 8eb131447d96

Provenance: formalization of a published result. Source: arXiv:2611.02374, Def. 2.1

A function f from the Boolean hypercube to {0, ..., k} is submodular if f(x ∨ y) + f(x ∧ y) ≤ f(x) + f(y) for all x, y in {0, 1}^n when embedded into ℝ.
-/

/-- Submodularity of a function on the Boolean hypercube into {0, ..., k} embedded in ℝ. -/
def is_submodular_cube {n k : ℕ} (f : CubeFunc n k) : Prop := ∀ x y : Fin n → Bool, (f (x ⊔ y) : ℝ) + (f (x ⊓ y) : ℝ) ≤ (f x : ℝ) + (f y : ℝ)
