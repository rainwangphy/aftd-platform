import AFTD.Prelude

/-!
# is_rank_one_product

Topic: proof_complexity   Node: 760e7ea3d9e2

Provenance: formalization of a published result. Source: arXiv:2611.01055, Section 2.3, Eq. (2)

A function R on the n-dimensional Boolean cube is a nonnegative rank-one product if it factors as the product of n nonnegative one-variable functions.
-/

/-- A rank-one product function on {0, 1}^n with nonnegative factors. -/
def is_rank_one_product {n : ℕ} (R : (Fin n → Bool) → ℝ) : Prop := ∃ g : Fin n → Bool → ℝ, (∀ i b, 0 ≤ g i b) ∧ ∀ τ, R τ = ∏ i : Fin n, g i (τ i)
