import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsStarLike
import AFTD.Kb.Tcs.SimpleGraphLeafNeighborCount
import AFTD.Kb.Tcs.DominatingAverageStabilityPathFiveDecidable

/-!
# dominating_average_stability_path_five_delete_endpoint

Topic: graphs   Node: 75b97f5455bc

Provenance: helper lemma. Finite sharpness certificate for the original OP-544 / IN-263 stability question. arXiv:2208.10475v2 Theorem2.9 supplies the extremal background. This formalizes the already computationally observed P5 obstruction to a smaller coefficient, not a proof of the universal bound or a research advance.

Deleting an endpoint from the five-vertex path leaves a star-like induced graph.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem dominating_average_stability_path_five_delete_endpoint :
    letI := dominating_average_stability_path_five_decidable
    simple_graph_is_star_like
      ((SimpleGraph.pathGraph 5).induce (({0} : Finset (Fin 5))ᶜ : Set (Fin 5))) := by
  unfold simple_graph_is_star_like simple_graph_leaf_neighbor_count
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  decide +kernel
