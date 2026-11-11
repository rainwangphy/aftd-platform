import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinBordaManipulationGain

/-!
# round_robin_expected_manipulation_gain

Topic: fair_division   Node: 05a5c531315b

Provenance: formalization of a published result. Source: A Social Welfare Optimal Sequential Allocation Procedure

The real-valued expected normalized strategic manipulation gain, returning a real number defined as the sum over all ranking pairs p in (Fin m ≃ Fin m) × (Fin m ≃ Fin m) of round_robin_borda_manipulation_gain m p.1 p.2, divided by ((Fintype.card (Fin m ≃ Fin m))^2 : ℝ).
-/

/-- Expected normalized manipulation gain in ℝ under independent uniform random rankings of m goods. -/
noncomputable def round_robin_expected_manipulation_gain (m : ℕ) : ℝ :=
  (∑ p : (Fin m ≃ Fin m) × (Fin m ≃ Fin m), round_robin_borda_manipulation_gain m p.1 p.2) /
    ((Fintype.card (Fin m ≃ Fin m))^2 : ℝ)
