import AFTD.Prelude

/-!
# gpa_simplex

Topic: mechanism_design   Node: dfe471c63c72

The probability simplex Δ_k.
-/

open Finset in
/-- The probability simplex `Δ_k`. -/
def gpa_simplex (k : ℕ) : Set (Fin k → ℝ) :=
  {σ | (∀ i, 0 ≤ σ i) ∧ ∑ i, σ i = 1}
