import AFTD.Prelude
import AFTD.Kb.Optimization.MatrixPsdRank
import AFTD.Kb.Optimization.MatrixHasPsdFactorizationHadamardSelf
import AFTD.Kb.Optimization.MatrixPsdRankHadamardSelfLeRank

/-!
# matrix_psd_rank_le_rank_of_hadamard_eq

Topic: integer_programming   Node: ae85cdcc4419

Provenance: formalization of a published result. Source: arXiv:2610.04498 Lemma 2.1 -- Rank-sensitive vertex bounds for semidefinite lifts

For finite types m and n, if M is an entrywise nonnegative real matrix (∀ i j, 0 ≤ M i j) and R is a real matrix such that M = Matrix.hadamard R R, then the positive semidefinite rank of M is at most the ordinary rank of R (matrix_psd_rank M ≤ Matrix.rank R).
-/

/-- If M is a nonnegative real matrix equal to the Hadamard square of R, then the positive semidefinite rank of M is at most the rank of R. -/
theorem matrix_psd_rank_le_rank_of_hadamard_eq {m n : Type*} [Fintype m] [Fintype n] (M R : Matrix m n ℝ) (hM : ∀ i j, 0 ≤ M i j) (hR : M = Matrix.hadamard R R) : matrix_psd_rank M ≤ Matrix.rank R := by
  subst hR
  exact matrix_psd_rank_hadamard_self_le_rank R
