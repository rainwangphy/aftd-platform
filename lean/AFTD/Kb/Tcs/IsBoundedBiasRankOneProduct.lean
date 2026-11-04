import AFTD.Prelude

/-!
# is_bounded_bias_rank_one_product

Topic: proof_complexity   Node: c72b811304e4

Provenance: formalization of a published result. Source: arXiv:2611.01055, Definition 2.5 and Lemma 2.6

A function R : (Fin n → Bool) → ℝ on the n-dimensional Boolean cube is a bounded-bias rank-one product (is_bounded_bias_rank_one_product R) if there exists a family of nonnegative one-variable functions g : Fin n → Bool → ℝ such that for every coordinate i : Fin n, either g i true = 0, g i false = 0, or g i true = g i false, and R τ = ∏ i : Fin n, g i (τ i) for all truth assignments τ : Fin n → Bool.
-/

/-- A function R on the n-dimensional Boolean cube is a bounded-bias rank-one product if it factors as a nonnegative product whose one-variable factors have biases in {0, 1/2, 1}. -/
def is_bounded_bias_rank_one_product {n : ℕ} (R : (Fin n → Bool) → ℝ) : Prop := ∃ g : Fin n → Bool → ℝ,
    (∀ i b, 0 ≤ g i b) ∧
    (∀ i, g i true = 0 ∨ g i false = 0 ∨ g i true = g i false) ∧
    ∀ τ, R τ = ∏ i : Fin n, g i (τ i)
