import AFTD.Prelude
import AFTD.Kb.Tcs.G5Adj

/-!
# b5_quotient_matrix

Topic: graphs   Node: 8cde780d8ab7

Provenance: formalization of a published result. Source: arXiv:2610.21388 (Stronger spectral bound for clique number), Theorem 2.3 (t = 5)

M_ii = n_i - 1, M_ij = a_ij n_j (a = adjacency of G_5); the eigenvalues of M are those of B_5 other than -1 (Theorem 2.3 of arXiv:2610.21388), so tr(M^2) is their sum of squares.
-/

/-- The quotient matrix `M` of `B₅(n₀, …, n₄)` (arXiv:2610.21388, Theorem 2.3): `M i i = n i - 1`, `M i j = n j` for adjacent blocks and `0` otherwise. Its eigenvalues are the adjacency eigenvalues of `B₅` other than `-1`. -/
noncomputable def b5_quotient_matrix (n : Fin 5 → ℕ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => if i = j then (n i : ℝ) - 1 else if g5_adj i j then (n j : ℝ) else 0
