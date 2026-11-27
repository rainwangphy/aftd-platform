import AFTD.Prelude
import AFTD.Kb.Physics.GeometricThermoProbeError
import AFTD.Kb.Physics.GeometricGibbs
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# geometric_thermo_missed_error

Topic: quantum_mechanics   Node: 5c0c3e869a12

Provenance: formalization of a published result. Source: arXiv:2610.35433

For dimension N, parameter q, and probe set F : Finset ℕ, the worst-case missed error geometric_thermo_missed_error N q F is the supremum over all x ∈ stdSimplex ℝ (Fin N) and all y ∈ stdSimplex ℝ (Fin N) satisfying Antitone (fun i : Fin N => y i / geometric_gibbs N q i) of geometric_thermo_probe_error N q (Finset.Ioo 0 N) x y - geometric_thermo_probe_error N q F x y.
-/

/-- Worst-case missed conversion error for probe set F. -/
noncomputable def geometric_thermo_missed_error (N : ℕ) (q : ℝ) (F : Finset ℕ) : ℝ := ⨆ (x ∈ stdSimplex ℝ (Fin N)) (y ∈ {v ∈ stdSimplex ℝ (Fin N) | Antitone (fun i : Fin N => v i / geometric_gibbs N q i)}), (geometric_thermo_probe_error N q (Finset.Ioo 0 N) x y - geometric_thermo_probe_error N q F x y)
