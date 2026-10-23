import AFTD.Prelude

/-!
# quinticDecoder

Topic: circuits   Node: 1b24b4f7eab5

Provenance: formalization of a published result. Source: arXiv:2610.19174 Theorem 3.2.1

The formal polynomial quinticDecoder of type Polynomial ℝ is defined as Polynomial.C (1 / 15 : ℝ) * (Polynomial.C 2 * Polynomial.X ^ 5 - Polynomial.C 5 * Polynomial.X ^ 4 - Polynomial.C 10 * Polynomial.X ^ 3 + Polynomial.C 20 * Polynomial.X ^ 2 + Polynomial.C 8 * Polynomial.X).
-/

/-- The quintic polynomial used to decode ternary integer lifts. -/
noncomputable def quinticDecoder : Polynomial ℝ := Polynomial.C (1 / 15 : ℝ) * (Polynomial.C 2 * Polynomial.X ^ 5 -
    Polynomial.C 5 * Polynomial.X ^ 4 -
    Polynomial.C 10 * Polynomial.X ^ 3 +
    Polynomial.C 20 * Polynomial.X ^ 2 +
    Polynomial.C 8 * Polynomial.X)
