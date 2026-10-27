import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphStarLikeDeletionNumber
import AFTD.Kb.Tcs.DominatingAverageStabilityPathFiveDecidable
import AFTD.Kb.Tcs.DominatingAverageStabilityPathFiveMean
import AFTD.Kb.Tcs.DominatingAverageStabilityPathFiveDeletion

/-!
# dominating_average_stability_constant_lower_bound

Topic: graphs   Node: 0443061a9583

Provenance: helper lemma. Finite sharpness certificate for the original OP-544 / IN-263 stability question. arXiv:2208.10475v2 Theorem2.9 supplies the extremal background. This formalizes the already computationally observed P5 obstruction to a smaller coefficient, not a proof of the universal bound or a research advance.

Any multiplicative stability coefficient valid on the five-vertex path is at least51/5. This is a necessary constant, not the universal stability inequality.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem dominating_average_stability_constant_lower_bound (C : ℚ) :
    letI := dominating_average_stability_path_five_decidable
    (simple_graph_star_like_deletion_number (SimpleGraph.pathGraph 5) : ℚ) ≤
      C * (2 * (Fintype.card (Fin 5) : ℚ) / 3 -
        simple_graph_avg_dominating_order (SimpleGraph.pathGraph 5)) → 51/5 ≤ C := by
  letI := dominating_average_stability_path_five_decidable
  rw [dominating_average_stability_path_five_deletion,
      dominating_average_stability_path_five_mean]
  norm_num
  intro h
  linarith
