import AFTD.Prelude

/-!
# weighted_catalan_poly

Topic: elementary_number_theory   Node: bd28c2f68c39

Provenance: formalization of a published result. Source: arXiv:2611.26953, Section 1.2

For each integer parameter t, the polynomial function b_t from natural numbers to integers is defined by b_t(x) = (4t + 1)x^3 - x^2 + 1.
-/

/-- The cubic polynomial family b_t(x) = (4t+1)x^3 - x^2 + 1 providing counterexamples to the 2-adic valuation conjecture. -/
def weighted_catalan_poly (t : ℤ) (x : ℕ) : ℤ := (4 * t + 1) * (x : ℤ) ^ 3 - (x : ℤ) ^ 2 + 1
