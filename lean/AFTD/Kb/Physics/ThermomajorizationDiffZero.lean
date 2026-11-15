import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationDiff
import AFTD.Kb.Tcs.TeamVBounds

/-!
# thermomajorization_diff_zero

Topic: quantum_mechanics   Node: 6175a012e51e

Provenance: helper lemma. step towards thermomajorization_optimal_nonadaptive_probe_budget_scaling

For any dimension n and population vectors x and y, the thermomajorization prefix difference thermomajorization_diff x y 0 at rank 0 equals 0.
-/

/-- thermomajorization_diff at rank 0 vanishes for any population vectors. -/
lemma thermomajorization_diff_zero {n : ℕ} (x y : Fin n → ℝ) :
    thermomajorization_diff x y 0 = 0 := by first | exact team_v_bounds | (apply team_v_bounds <;> assumption) | (apply team_v_bounds <;> simp_all) | simpa using team_v_bounds | (simp only [thermomajorization_diff] at *; first | exact team_v_bounds | (apply team_v_bounds <;> assumption) | (apply team_v_bounds <;> simp_all) | simpa using team_v_bounds)
