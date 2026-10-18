import AFTD.Prelude

/-!
# b3_quotient_matrix

Topic: graphs   Node: 04d32900fea3

Provenance: formalization of a published result. Source: arXiv:2610.21388 (Stronger spectral bound for clique number), Theorem 2.3 (odd case, s = 1): the matrix M

The 3x3 quotient matrix M = [[n_0 - 1, 0, n_2], [0, n_1 - 1, n_2], [n_0, n_1, n_2 - 1]] of B_3(n_0, n_1, n_2), whose three eigenvalues are the adjacency eigenvalues of B_3 different from -1.
-/

/-- The quotient matrix `M` of the partition of `B₃(n₀, n₁, n₂)` into its three cliques: entry `(i, i)` is `nᵢ - 1`, entry `(i, j)` is `nⱼ` when blocks `i ≠ j` are joined and `0` otherwise. Its eigenvalues are the adjacency eigenvalues of `B₃` other than `-1`. -/
noncomputable def b3_quotient_matrix (n : Fin 3 → ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(n 0 : ℝ) - 1, 0, n 2; 0, (n 1 : ℝ) - 1, n 2; n 0, n 1, (n 2 : ℝ) - 1]
