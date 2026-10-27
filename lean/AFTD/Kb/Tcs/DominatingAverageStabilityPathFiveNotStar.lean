import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsStarLike
import AFTD.Kb.Tcs.SimpleGraphLeafNeighborCount
import AFTD.Kb.Tcs.DominatingAverageStabilityPathFiveDecidable

/-!
# dominating_average_stability_path_five_not_star

Topic: graphs   Node: 8a500f8a2e71

Provenance: helper lemma. Finite sharpness certificate for the original OP-544 / IN-263 stability question. arXiv:2208.10475v2 Theorem2.9 supplies the extremal background. This formalizes the already computationally observed P5 obstruction to a smaller coefficient, not a proof of the universal bound or a research advance.

The five-vertex path is not star-like.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem dominating_average_stability_path_five_not_star :
    letI := dominating_average_stability_path_five_decidable
    ¬ simple_graph_is_star_like (SimpleGraph.pathGraph 5) := by
  unfold simple_graph_is_star_like simple_graph_leaf_neighbor_count
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  decide +kernel
