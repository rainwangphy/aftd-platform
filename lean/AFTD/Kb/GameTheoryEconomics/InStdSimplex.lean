import AFTD.Prelude

/-!
# in_std_simplex

Topic: general_equilibrium   Node: e01d427b45f2

A vector lies in the standard simplex: nonnegative entries summing to 1.
-/

/-- `w` lies in the standard simplex: nonnegative entries summing to 1. -/
def in_std_simplex {n : ℕ} (w : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1
