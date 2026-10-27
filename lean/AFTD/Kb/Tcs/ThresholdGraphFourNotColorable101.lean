import AFTD.Prelude
import AFTD.Kb.Tcs.GaleDistanceGraph
import AFTD.Kb.Tcs.Threshold101Coords
import AFTD.Kb.Tcs.Threshold101Edges
import AFTD.Kb.Tcs.Threshold101CoordsInjective
import AFTD.Kb.Tcs.Threshold101DiameterSquaredLe
import AFTD.Kb.Tcs.Threshold101EdgesSquaredGe
import AFTD.Kb.Tcs.Threshold101NoFourColoring
import AFTD.Kb.Tcs.ThresholdGraphNotFourColorableOfIntegerWitness

/-!
# threshold_graph_four_not_colorable_101

Topic: combinatorics   Node: fed12533cc4a

Provenance: helper lemma. arXiv:2610.28828 -- A counterexample to Gale's conjecture in $\mathbb{R}^3$, Theorem 2

There exists a finite subset V of 3-dimensional Euclidean space with cardinality 101 and strictly positive diameter such that the distance threshold graph on V at threshold 0.88928 times the diameter of V admits no proper 4-coloring.
-/

/-- There exists a 101-point subset in 3D Euclidean space with positive diameter whose distance threshold graph at threshold 0.88928 times diameter is not 4-colorable. -/
theorem threshold_graph_four_not_colorable_101 :
    ∃ V : Finset (EuclideanSpace ℝ (Fin 3)),
      V.card = 101 ∧
      0 < Metric.diam (V : Set (EuclideanSpace ℝ (Fin 3))) ∧
      ¬ (gale_distance_graph V ((88928 / 100000 : ℝ) * Metric.diam (V : Set (EuclideanSpace ℝ (Fin 3))))).Colorable 4 := by
  exact threshold_graph_not_four_colorable_of_integer_witness 101 100000000000000100 7908209857886758229068357146803906 (by norm_num)
    (88928 / 100000) (by norm_num) threshold101_coords threshold101_edges
    threshold101_coords_injective threshold101_diameter_squared_le threshold101_edges_squared_ge
    (by norm_num) threshold101_no_four_coloring 0 1 (by decide)
