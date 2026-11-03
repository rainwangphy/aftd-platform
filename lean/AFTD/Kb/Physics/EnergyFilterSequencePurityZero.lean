import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterSequencePurity

/-!
# energy_filter_sequence_purity_zero

Topic: statistical_mechanics   Node: 5eca7b79cf03

Provenance: helper lemma. arXiv:2405.02158 Energy-filtered quantum states and the emergence of non-local correlations

For any natural number k, the energy-filtered purity energy_filter_sequence_purity 0 k of the identically zero sequence 0 at parameter k is equal to zero.
-/

/-- Sanity lemma: the sequence purity vanishes when the filter sequence is identically zero. -/
theorem energy_filter_sequence_purity_zero (k : ℕ) :
    energy_filter_sequence_purity 0 k = 0 := by
  unfold energy_filter_sequence_purity
  let M : Matrix (Fin (2 * k) → Bool) (Fin (2 * k) → Bool) ℝ :=
    fun sA sB =>
      (0 : ℤ → ℝ) (2 * (k : ℤ) - (∑ j : Fin (2 * k), if sA j then 1 else 0) -
        (∑ j : Fin (2 * k), if sB j then 1 else 0))
  change ((M * M.transpose) * (M * M.transpose)).trace / ((M * M.transpose).trace) ^ 2 = 0
  have hM : M = 0 := by
    ext i j
    simp [M]
  rw [hM]
  simp
