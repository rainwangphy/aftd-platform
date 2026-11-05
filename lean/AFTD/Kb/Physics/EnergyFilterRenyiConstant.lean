import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterFourierSymbol
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS2

/-!
# energy_filter_renyi_constant

Topic: statistical_mechanics   Node: e24787761a9d

Provenance: formalization of a published result. Source: knowledgebase, OP-1115

For a filter sequence a : ℤ → ℝ and real exponent q, energy_filter_renyi_constant a q is (4 / Real.sqrt (2 * Real.pi)) ^ q * Real.sqrt (Real.pi / (8 * q)) * ((1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖energy_filter_fourier_symbol a θ‖ ^ (2 * q)) / (energy_filter_sequence_lattice_s2 a ^ q).
-/

/-- The asymptotic Renyi-q constant (4/√(2π))^q √(π/(8q)) (1/(2π)) ∫_0^(2π) |A(θ)|^(2q) dθ / S^q for energy filters. -/
noncomputable def energy_filter_renyi_constant (a : ℤ → ℝ) (q : ℝ) : ℝ :=
  let S := energy_filter_sequence_lattice_s2 a
  let Cq := (4 / Real.sqrt (2 * Real.pi)) ^ q * Real.sqrt (Real.pi / (8 * q))
  let integ := (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
    ‖energy_filter_fourier_symbol a θ‖ ^ (2 * q)
  Cq * integ / (S ^ q)
