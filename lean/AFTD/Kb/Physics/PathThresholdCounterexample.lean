import AFTD.Prelude
import AFTD.Kb.Physics.ParityCouplingProfileLocallyValid

/-!
# path_threshold_counterexample

Topic: quantum_mechanics   Node: 3a167151fc7b

Provenance: helper lemma. Exact counterexample to an auxiliary OP-827 proof route, experiments 22515 and 22523.

The exact logarithmic weights and signed cumulative count in the path threshold counterexample satisfy the asserted inequalities.
-/

theorem path_threshold_counterexample :
    (7 : ℤ) ≤ 17 + 2 ∧ 2 ≤ 7 + 14 ∧ 14 ≤ 2 + 18 ∧
    2 < 19 ∧ 19 < 20 ∧ 20 < 37 ∧
    (1 : ℤ) - 1 - 1 < 0 := by first | exact parity_coupling_profile_locally_valid | (apply parity_coupling_profile_locally_valid <;> assumption) | (apply parity_coupling_profile_locally_valid <;> simp_all) | simpa using parity_coupling_profile_locally_valid
