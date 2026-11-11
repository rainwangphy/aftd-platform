import AFTD.Prelude

/-!
# polynomial_is_unimodal

Topic: graphs   Node: 9d73b60e0c61

Provenance: formalization of a published result. Source: arXiv:2611.11352 Section 1

A polynomial with natural coefficients is unimodal if its coefficient sequence is weakly increasing up to some index and weakly decreasing thereafter.
-/

/-- Unimodality of a polynomial with natural coefficients. -/
def polynomial_is_unimodal (p : Polynomial ℕ) : Prop := ∃ m : ℕ, (∀ ⦃i j⦄, i ≤ j → j ≤ m → p.coeff i ≤ p.coeff j) ∧
           (∀ ⦃i j⦄, m ≤ i → i ≤ j → p.coeff j ≤ p.coeff i)
