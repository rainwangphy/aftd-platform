import AFTD.Prelude
import AFTD.Kb.Optimization.KSubmodLe

/-!
# is_k_submod_monotone

Topic: submodular   Node: 1efc2a06fa1d

Provenance: formalization of a published result. Source: arXiv:2610.26677, line 107

A function f : (Fin n → Option (Fin k)) → ℝ is monotone if x ≤ y under the componentwise order implies f x ≤ f y.
-/

/-- Monotonicity of a function on assignments with respect to the componentwise order. -/
def is_k_submod_monotone {n k : ℕ} (f : (Fin n → Option (Fin k)) → ℝ) : Prop := ∀ x y, k_submod_le x y → f x ≤ f y
