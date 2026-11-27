import AFTD.Prelude
import AFTD.Kb.Physics.GeometricThermoMissedError

/-!
# geometric_thermo_minimax_error

Topic: quantum_mechanics   Node: 3441991891d5

Provenance: formalization of a published result. Source: arXiv:2610.35433

For dimension N, budget m : ℕ, and parameter q : ℝ, the minimax missed error geometric_thermo_minimax_error N m q is the infimum of geometric_thermo_missed_error N q F over all subsets F of Finset.Ioo 0 N with cardinality m.
-/

/-- Minimax missed conversion error R_N(m, q) for m probes among N-1 ranks. -/
noncomputable def geometric_thermo_minimax_error (N m : ℕ) (q : ℝ) : ℝ := ⨅ F ∈ Finset.powersetCard m (Finset.Ioo 0 N), geometric_thermo_missed_error N q F
