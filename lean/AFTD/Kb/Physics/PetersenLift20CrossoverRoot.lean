import AFTD.Prelude
import AFTD.Kb.Physics.PetersenPolyVariancePerVertex
import AFTD.Kb.Physics.Lift20PolyVariancePerVertex

/-!
# petersen_lift20_crossover_root

Topic: statistical_mechanics   Node: 0576bc7bce27

Provenance: formalization of a published result. Source: arXiv:1806.02146

The crossover activity x_* defined as the infimum of all positive real numbers x > 0 such that the per-vertex hard-core variance of the 20-vertex Petersen 2-lift lift20_poly_variance_per_vertex x equals the per-vertex hard-core variance of the Petersen graph petersen_poly_variance_per_vertex x.
-/

/-- The first strictly positive crossover activity between the 20-vertex two-lift variance and the Petersen graph variance. -/
noncomputable def petersen_lift20_crossover_root : ℝ :=
  sInf {x : ℝ | 0 < x ∧ lift20_poly_variance_per_vertex x = petersen_poly_variance_per_vertex x}
