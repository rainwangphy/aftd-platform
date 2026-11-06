import AFTD.Prelude

/-!
# tableau_weight

Topic: combinatorics   Node: 8c33d94417b7

Provenance: formalization of a published result. Source: arXiv:2611.07715 Section 5.1

For a finite diagram D : Finset (ℕ × ℕ) and a filling M : D → ℕ, tableau_weight D M is the multivariate polynomial in MvPolynomial ℕ ℤ defined by the product over all cells u : D of the indeterminate MvPolynomial.X (M u).
-/

/-- The monomial weight x^M of a filling M on a diagram D, defined as the product of variables X (M u) over all cells u in D. -/
noncomputable def tableau_weight (D : Finset (ℕ × ℕ)) (M : D → ℕ) : MvPolynomial ℕ ℤ := ∏ u : D, MvPolynomial.X (M u)
