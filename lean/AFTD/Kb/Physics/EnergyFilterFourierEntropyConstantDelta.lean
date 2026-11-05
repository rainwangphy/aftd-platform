import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterFourierEntropyConstant
import AFTD.Kb.Physics.EnergyFilterFourierSymbol
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS2

/-!
# energy_filter_fourier_entropy_constant_delta

Topic: statistical_mechanics   Node: 1be83fa2d6ff

Provenance: formalization of a published result. Source: arXiv:2405.02158

For the Kronecker delta filter delta j = (if j = 0 then 1 else 0), the Fourier entropy constant energy_filter_fourier_entropy_constant delta is equal to 0.
-/

/-- The Fourier entropy constant vanishes for the Kronecker delta filter. -/
theorem energy_filter_fourier_entropy_constant_delta :
    let delta : ℤ → ℝ := fun j => if j = 0 then 1 else 0
    energy_filter_fourier_entropy_constant delta = 0 := by
  dsimp only
  rw [energy_filter_fourier_entropy_constant]
  dsimp only
  have hS2 : energy_filter_sequence_lattice_s2 (fun j : ℤ => if j = 0 then 1 else 0) = 1 := by
    simp only [energy_filter_sequence_lattice_s2]
    rw [tsum_eq_single 0]
    · simp
    · intro b hb; simp [hb]
  have hsym : ∀ θ : ℝ, energy_filter_fourier_symbol (fun j : ℤ => if j = 0 then 1 else 0) θ = 1 := by
    intro θ
    simp only [energy_filter_fourier_symbol]
    rw [tsum_eq_single 0]
    · simp
    · intro b hb; simp [hb]
  simp only [hS2, hsym]
  simp
