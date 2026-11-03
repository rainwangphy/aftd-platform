import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterSequencePurity

/-!
# energy_filter_sequence_purity_scale

Topic: statistical_mechanics   Node: 6adef93d01cb

Provenance: original. Related work: arXiv:2405.02158 Energy-filtered quantum states and the emergence of non-local correlations

For any sequence filter a : ℤ → ℝ, any nonzero real scalar c, and any natural number k, the purity of the scaled filter energy_filter_sequence_purity (fun j => c * a j) k equals energy_filter_sequence_purity a k.
-/

/-- The energy-filtered purity is invariant under nonzero scalar multiplication of the filter sequence. -/
theorem energy_filter_sequence_purity_scale (a : ℤ → ℝ) (c : ℝ) (hc : c ≠ 0) (k : ℕ) :
    energy_filter_sequence_purity (fun j => c * a j) k = energy_filter_sequence_purity a k := by
  open Matrix in
  dsimp only [energy_filter_sequence_purity]
  let M : Matrix (Fin (2 * k) → Bool) (Fin (2 * k) → Bool) ℝ :=
    fun sA sB => a ((2 * ↑k - ∑ j, if sA j = true then 1 else 0) - ∑ j, if sB j = true then 1 else 0)
  have hM : (fun sA sB => c * a ((2 * ↑k - ∑ j, if sA j = true then 1 else 0) - ∑ j, if sB j = true then 1 else 0)) = c • M := rfl
  rw [hM]
  let R := M * Mᵀ
  have hR : (c • M) * (c • M)ᵀ = (c ^ 2) • R := by
    rw [transpose_smul, smul_mul, Matrix.mul_smul, smul_smul, sq]
  rw [hR]
  have hR2 : ((c ^ 2) • R) * ((c ^ 2) • R) = (c ^ 4) • (R * R) := by
    rw [smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    ring
  rw [hR2]
  rw [trace_smul, trace_smul, smul_eq_mul, smul_eq_mul]
  have hsq : (c ^ 2 * R.trace) ^ 2 = c ^ 4 * R.trace ^ 2 := by ring
  rw [hsq]
  exact mul_div_mul_left _ _ (pow_ne_zero 4 hc)
