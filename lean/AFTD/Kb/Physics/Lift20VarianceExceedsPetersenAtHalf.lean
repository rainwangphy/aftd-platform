import AFTD.Prelude
import AFTD.Kb.Physics.PetersenPolyVariancePerVertex
import AFTD.Kb.Physics.Lift20PolyVariancePerVertex

/-!
# lift20_variance_exceeds_petersen_at_half

Topic: statistical_mechanics   Node: e1800d6ac774

Provenance: formalization of a published result. Source: arXiv:1806.02146

At activity x = 1/2, the per-vertex hard-core variance of the Petersen graph petersen_poly_variance_per_vertex (1/2) is strictly less than that of the 20-vertex Petersen 2-lift lift20_poly_variance_per_vertex (1/2).
-/

/-- At activity 1/2, the per-vertex hard-core variance of the Petersen graph is strictly less than that of the 20-vertex lift. -/
theorem lift20_variance_exceeds_petersen_at_half :
    petersen_poly_variance_per_vertex (1/2) < lift20_poly_variance_per_vertex (1/2) := by
  unfold petersen_poly_variance_per_vertex lift20_poly_variance_per_vertex
  norm_num
