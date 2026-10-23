import AFTD.Prelude

/-!
# hn_poly

Topic: graphs   Node: cd4af93e8ee4

Provenance: formalization of a published result. Source: arXiv:2610.18636:210

For every natural number n, hn_poly n is the cubic polynomial q_n(x) = x^3 - n*x^2 - (2*n^2 - n - 1)*x + (n^2 - n) over the real numbers.
-/

/-- The cubic polynomial q_n(x) associated with the competitor graph H_n. -/
noncomputable def hn_poly (n : ℕ) : Polynomial ℝ :=
  Polynomial.X ^ 3 - Polynomial.C (n : ℝ) * Polynomial.X ^ 2 -
    Polynomial.C (2 * (n : ℝ) ^ 2 - (n : ℝ) - 1) * Polynomial.X +
    Polynomial.C ((n : ℝ) ^ 2 - (n : ℝ))
