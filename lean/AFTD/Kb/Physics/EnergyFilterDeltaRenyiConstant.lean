import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterRenyiConstant
import AFTD.Kb.Physics.EnergyFilterFourierSymbol
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS2
import AFTD.Kb.Physics.EnergyFilterDeltaLatticeSums
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS4
import AFTD.Kb.Physics.EnergyFilterSequencePurityConstant

/-!
# energy_filter_delta_renyi_constant

Topic: statistical_mechanics   Node: 334e24273bbd

Provenance: helper lemma. knowledgebase, OP-1115

For the Kronecker delta filter delta : ℤ → ℝ defined by delta 0 = 1 and delta j = 0 for j ≠ 0, and any real q > 0, energy_filter_renyi_constant delta q equals (4 / Real.sqrt (2 * Real.pi)) ^ q * Real.sqrt (Real.pi / (8 * q)).
-/

/-- Exact evaluation of the Renyi constant for the Kronecker delta energy filter. -/
theorem energy_filter_delta_renyi_constant (q : ℝ) (hq : 0 < q) :
    let delta : ℤ → ℝ := fun j => if j = 0 then 1 else 0
    energy_filter_renyi_constant delta q =
      (4 / Real.sqrt (2 * Real.pi)) ^ q * Real.sqrt (Real.pi / (8 * q)) := by
  intro delta
  have hfour : ∀ θ : ℝ, energy_filter_fourier_symbol delta θ = 1 := by
    intro θ
    simp only [energy_filter_fourier_symbol]
    rw [tsum_eq_single (0:ℤ)]
    · simp [delta]
    · intro b hb
      simp [delta, hb]
  have hnorm : ∀ θ : ℝ, ‖energy_filter_fourier_symbol delta θ‖ ^ (2*q) = 1 := by
    intro θ
    rw [hfour θ]
    simp
  have hint : ∫ θ in (0:ℝ)..(2*Real.pi), ‖energy_filter_fourier_symbol delta θ‖ ^ (2*q) = 2*Real.pi := by
    simp only [hnorm]
    rw [intervalIntegral.integral_const]
    simp
  have hs2 : energy_filter_sequence_lattice_s2 delta = 1 := by
    have h := energy_filter_delta_lattice_sums
    simp only at h
    exact h.1
  simp only [energy_filter_renyi_constant]
  rw [hint, hs2]
  rw [Real.one_rpow]
  rw [div_one]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
