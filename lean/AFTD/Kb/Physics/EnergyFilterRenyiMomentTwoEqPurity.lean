import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterRenyiMoment
import AFTD.Kb.Physics.EnergyFilterSequencePurity
import AFTD.Kb.Tcs.MatrixIsHermitianSumEigenvaluesEqTrace

/-!
# energy_filter_renyi_moment_two_eq_purity

Topic: statistical_mechanics   Node: b0ea7eb52015

Provenance: helper lemma. knowledgebase, OP-1115

For any sequence filter a : ℤ → ℝ and any natural number k, the Renyi-2 moment energy_filter_renyi_moment a k 2 equals the bipartite purity energy_filter_sequence_purity a k.
-/

/-- For a Hermitian real matrix `A`, the trace of `A * A` is the sum of the squares of its eigenvalues. -/
private lemma trace_mul_self_eq_sum_eigenvalues_sq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, (hA.eigenvalues i)^2 := by
  let U : Matrix n n ℝ := ↑hA.eigenvectorUnitary
  let D : Matrix n n ℝ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hUU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self hA.eigenvectorUnitary
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  change (U * D * star U * (U * D * star U)).trace = _
  have hid : U * D * star U * (U * D * star U) = U * (D * D) * star U := by
    calc
      U * D * star U * (U * D * star U) = U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * (D * D) * star U := by rw [hUU]; noncomm_ring
  rw [hid, Matrix.trace_mul_cycle]
  rw [hUU]
  simp only [one_mul]
  change (D * D).trace = _
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [pow_two]

/-- Equivalence between the Renyi moment at q = 2 and the Renyi-2 bipartite purity. -/
theorem energy_filter_renyi_moment_two_eq_purity (a : ℤ → ℝ) (k : ℕ) :
    energy_filter_renyi_moment a k 2 = energy_filter_sequence_purity a k := by
  unfold energy_filter_renyi_moment energy_filter_sequence_purity
  dsimp only
  let M : Matrix (Fin (2 * k) → Bool) (Fin (2 * k) → Bool) ℝ :=
    fun sA sB => a (2 * (k : ℤ) - (∑ j : Fin (2 * k), if sA j then 1 else 0)
      - (∑ j : Fin (2 * k), if sB j then 1 else 0))
  let R : Matrix (Fin (2 * k) → Bool) (Fin (2 * k) → Bool) ℝ := M * M.transpose
  have hR : R.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M
  change (∑ s, hR.eigenvalues s ^ ((2:ℕ):ℝ)) / (∑ s, hR.eigenvalues s) ^ ((2:ℕ):ℝ)
      = (R * R).trace / R.trace ^ 2
  simp only [Real.rpow_natCast]
  rw [← trace_mul_self_eq_sum_eigenvalues_sq R hR]
  rw [← Matrix.IsHermitian.sum_eigenvalues_eq_trace hR]
  norm_num
