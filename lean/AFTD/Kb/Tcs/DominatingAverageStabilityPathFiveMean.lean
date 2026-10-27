import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSets
import AFTD.Kb.Tcs.DominatingAverageStabilityPathFiveDecidable

/-!
# dominating_average_stability_path_five_mean

Topic: graphs   Node: b6d0b71fca6c

Provenance: helper lemma. Finite sharpness certificate for the original OP-544 / IN-263 stability question. arXiv:2208.10475v2 Theorem2.9 supplies the extremal background. This formalizes the already computationally observed P5 obstruction to a smaller coefficient, not a proof of the universal bound or a research advance.

The five-vertex path has average dominating-set size55/17.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem dominating_average_stability_path_five_mean :
    letI := dominating_average_stability_path_five_decidable
    simple_graph_avg_dominating_order (SimpleGraph.pathGraph 5) = 55/17 := by
  unfold simple_graph_avg_dominating_order simple_graph_dominating_sets
  decide +kernel
