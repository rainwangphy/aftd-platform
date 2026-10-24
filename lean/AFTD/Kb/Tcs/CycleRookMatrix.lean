import AFTD.Prelude

/-!
# cycle_rook_matrix

Topic: combinatorics   Node: 9049c40c9f55

Provenance: helper lemma. step towards cycle_rook_poly_sq_sub

The Fibonacci transfer matrix M = !![1, X; 1, 0] over ℚ[X]; its powers satisfy the same recurrence as the cycle rook polynomials, and tr(M^m) is the m-cycle rook polynomial.
-/

/-- The 2x2 matrix !![1, X; 1, 0] over ℚ[X], whose power traces are the cycle rook polynomials. -/
noncomputable def cycle_rook_matrix : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) := !![(1 : Polynomial ℚ), (Polynomial.X : Polynomial ℚ); (1 : Polynomial ℚ), 0]
