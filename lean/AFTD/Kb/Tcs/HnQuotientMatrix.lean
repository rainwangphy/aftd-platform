import AFTD.Prelude

/-!
# hn_quotient_matrix

Topic: graphs   Node: 39cae1c5f6d7

Provenance: formalization of a published result. Source: arXiv:2610.18636:224

For every natural number n, hn_quotient_matrix n is the 4 by 4 real matrix whose row 0 is ![0, (n : ℝ), (n : ℝ), 1], row 1 is ![(n : ℝ) - 1, 0, (n : ℝ), 0], row 2 is ![(n : ℝ) - 1, (n : ℝ), 0, 0], and row 3 is ![(n : ℝ) - 1, 0, 0, 0].
-/

/-- The 4x4 quotient matrix B of H_n. -/
def hn_quotient_matrix (n : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, (n : ℝ), (n : ℝ), 1;
     (n : ℝ) - 1, 0, (n : ℝ), 0;
     (n : ℝ) - 1, (n : ℝ), 0, 0;
     (n : ℝ) - 1, 0, 0, 0]
