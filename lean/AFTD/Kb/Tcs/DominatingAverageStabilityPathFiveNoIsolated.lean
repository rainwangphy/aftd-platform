import AFTD.Prelude
import AFTD.Kb.Tcs.DominatingAverageStabilityPathFiveDecidable

/-!
# dominating_average_stability_path_five_no_isolated

Topic: graphs   Node: a17911a24ab0

Provenance: helper lemma. Finite sharpness certificate for the original OP-544 / IN-263 stability question. arXiv:2208.10475v2 Theorem2.9 supplies the extremal background. This formalizes the already computationally observed P5 obstruction to a smaller coefficient, not a proof of the universal bound or a research advance.

The five-vertex path has no isolated vertex.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem dominating_average_stability_path_five_no_isolated :
    letI := dominating_average_stability_path_five_decidable
    ∀ w, 0 < (SimpleGraph.pathGraph 5).degree w := by
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  decide +kernel
