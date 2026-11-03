import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS2
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS4
import AFTD.Kb.Physics.EnergyFilterSequencePurityConstant

/-!
# energy_filter_delta_lattice_sums

Topic: statistical_mechanics   Node: ae109a7265dd

Provenance: original. Related work: arXiv:2405.02158 Energy-filtered quantum states and the emergence of non-local correlations

For the Kronecker delta filter delta : ℤ → ℝ defined by delta 0 = 1 and delta j = 0 for j ≠ 0, the second-moment lattice sum energy_filter_sequence_lattice_s2 delta is 1, the fourth-moment convolution sum energy_filter_sequence_lattice_s4 delta is 1, and the asymptotic purity constant energy_filter_sequence_purity_constant delta is 2 / Real.sqrt Real.pi.
-/

/-- For the single-energy projector delta filter at zero, S_2 = 1, S_4 = 1, and the universal purity constant is 2/sqrt(pi). -/
theorem energy_filter_delta_lattice_sums :
    let delta : ℤ → ℝ := fun j => if j = 0 then 1 else 0
    energy_filter_sequence_lattice_s2 delta = 1 ∧
    energy_filter_sequence_lattice_s4 delta = 1 ∧
    energy_filter_sequence_purity_constant delta = 2 / Real.sqrt Real.pi := by
  dsimp only
  have hsum2 : (∑' (j : ℤ), (if j = 0 then (1:ℝ) else 0) ^ 2) = 1 := by simp
  have hinner : ∀ m : ℤ,
      (∑' (j : ℤ), (if j = 0 then (1:ℝ) else 0) * (if m - j = 0 then (1:ℝ) else 0))
        = (if m = 0 then (1:ℝ) else 0) := by
    intro m
    rw [tsum_eq_single (0:ℤ)]
    · simp
    · intro b hb
      simp [hb]
  have hsum4 : (∑' (m : ℤ), (∑' (j : ℤ),
      (if j = 0 then (1:ℝ) else 0) * (if m - j = 0 then (1:ℝ) else 0)) ^ 2) = 1 := by
    simp only [hinner]
    simp
  refine ⟨?_, ?_, ?_⟩
  · simp [energy_filter_sequence_lattice_s2]
  · simp only [energy_filter_sequence_lattice_s4]
    exact hsum4
  · simp only [energy_filter_sequence_purity_constant]
    rw [hsum2, hsum4]
    norm_num
