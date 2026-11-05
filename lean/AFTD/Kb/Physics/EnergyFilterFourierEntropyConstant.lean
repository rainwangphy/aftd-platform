import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterFourierSymbol
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS2

/-!
# energy_filter_fourier_entropy_constant

Topic: statistical_mechanics   Node: f84426a59a40

Provenance: formalization of a published result. Source: arXiv:2405.02158

For a real sequence a on Z, energy_filter_fourier_entropy_constant a is the integral over [0, 2 pi] of w(theta) log w(theta) dtheta / (2 pi), where w(theta) = |A(theta)|^2 / S2(a) and 0 log 0 = 0.
-/

/-- The filter-dependent Fourier entropy constant integral_0^(2 pi) w(theta) log w(theta) dtheta / (2 pi). -/
noncomputable def energy_filter_fourier_entropy_constant (a : ℤ → ℝ) : ℝ :=
  let S2 := energy_filter_sequence_lattice_s2 a
  (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
    let w := ‖energy_filter_fourier_symbol a θ‖^2 / S2
    if w = 0 then 0 else w * Real.log w
