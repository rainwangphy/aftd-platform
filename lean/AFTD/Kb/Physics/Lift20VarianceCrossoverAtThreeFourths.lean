import AFTD.Prelude
import AFTD.Kb.Physics.PetersenPolyVariancePerVertex
import AFTD.Kb.Physics.Lift20PolyVariancePerVertex

/-!
# lift20_variance_crossover_at_three_fourths

Topic: statistical_mechanics   Node: ecc08c768060

Provenance: formalization of a published result. Source: arXiv:1806.02146

At activity x = 3/4, the per-vertex hard-core variance of the 20-vertex Petersen 2-lift lift20_poly_variance_per_vertex (3/4) is strictly less than that of the Petersen graph petersen_poly_variance_per_vertex (3/4).
-/

/-- At activity 3/4, the per-vertex hard-core variance of the 20-vertex lift is strictly less than that of the Petersen graph. -/
theorem lift20_variance_crossover_at_three_fourths :
    lift20_poly_variance_per_vertex (3/4) < petersen_poly_variance_per_vertex (3/4) := by
  unfold lift20_poly_variance_per_vertex petersen_poly_variance_per_vertex
  norm_num
