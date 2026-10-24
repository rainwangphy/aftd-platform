import AFTD.Prelude
import AFTD.Kb.Optimization.PermutahedronSlackMatrix
import AFTD.Kb.Optimization.MatrixPsdRank
import AFTD.Kb.Optimization.MatrixHasPsdFactorization

/-!
# permutahedron_five_not_psd_factorization_six_of_rank_ge_seven

Topic: integer_programming   Node: c3a3923bc932

Provenance: helper lemma. arXiv:2610.04498 Sec. 8

If the positive semidefinite rank of the slack matrix of the standard five-element permutahedron is at least 7, then the slack matrix has no positive semidefinite factorization of size 6.
-/

/-- PSD rank at least 7 implies no size-6 PSD factorization for the 5-permutahedron. -/
theorem permutahedron_five_not_psd_factorization_six_of_rank_ge_seven (h : 7 ≤ matrix_psd_rank (permutahedron_slack_matrix 5)) : ¬ matrix_has_psd_factorization (permutahedron_slack_matrix 5) 6 := by
  intro hf
  have hle : matrix_psd_rank (permutahedron_slack_matrix 5) ≤ 6 := Nat.sInf_le hf
  omega
