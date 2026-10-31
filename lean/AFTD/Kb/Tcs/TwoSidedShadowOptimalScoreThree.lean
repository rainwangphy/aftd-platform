import AFTD.Prelude
import AFTD.Kb.Tcs.TwoSidedShadowOptimalScore

/-!
# two_sided_shadow_optimal_score_three

Topic: quantum   Node: 09f48b820790

Provenance: helper lemma. scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:378

Sanity check: the optimal shadow score on 3 qubits equals 99.
-/

/-- Sanity check: the optimal shadow score on 3 qubits equals 99. -/
theorem two_sided_shadow_optimal_score_three : two_sided_shadow_optimal_score 3 = 99 := rfl
