import AFTD.Prelude

/-!
# is_balanced_indicator

Topic: information   Node: 642321bb2c3e

Provenance: formalization of a published result. Source: arXiv:2611.00868, Section 1

A real-valued function f on the n-dimensional Boolean cube is a balanced Boolean indicator if f takes values in {0, 1} and its uniform expectation (1 / 2^n) * ∑ x, f x equals 1/2.
-/

open scoped BigOperators in
/-- A Boolean indicator function f : {0,1}^n -> {0,1} with expectation 1/2. -/
def is_balanced_indicator (n : ℕ) (f : (Fin n → Bool) → ℝ) : Prop := (∀ x, f x = 0 ∨ f x = 1) ∧ (1 / (2 : ℝ) ^ n) * ∑ x, f x = 1 / 2
