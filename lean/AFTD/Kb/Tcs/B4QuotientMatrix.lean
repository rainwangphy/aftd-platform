import AFTD.Prelude

/-!
# b4_quotient_matrix

Topic: graphs   Node: 2bff4f20e1c1

Provenance: formalization of a published result. Source: arXiv:2610.21388, Theorem 2.3

Given a function n : Fin 4 → ℕ of natural numbers, b4_quotient_matrix n is the 4x4 real matrix Matrix (Fin 4) (Fin 4) ℝ with entries: row 0 is ![(n 0 : ℝ) - 1, (n 1 : ℝ), 0, 0], row 1 is ![(n 0 : ℝ), (n 1 : ℝ) - 1, 0, (n 3 : ℝ)], row 2 is ![0, 0, (n 2 : ℝ) - 1, (n 3 : ℝ)], and row 3 is ![0, (n 1 : ℝ), (n 2 : ℝ), (n 3 : ℝ) - 1].
-/

/-- The 4x4 quotient matrix M of B_4(n), whose four eigenvalues are the adjacency eigenvalues of B_4 different from -1. -/
noncomputable def b4_quotient_matrix (n : Fin 4 → ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(n 0 : ℝ) - 1, (n 1 : ℝ), 0, 0;
     (n 0 : ℝ), (n 1 : ℝ) - 1, 0, (n 3 : ℝ);
     0, 0, (n 2 : ℝ) - 1, (n 3 : ℝ);
     0, (n 1 : ℝ), (n 2 : ℝ), (n 3 : ℝ) - 1]
