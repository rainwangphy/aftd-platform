import AFTD.Prelude
import AFTD.Kb.Tcs.DominatingOccupancy
import AFTD.Kb.Tcs.SimpleGraphAvgDominatingOrder
import AFTD.Kb.Tcs.DominatingPartitionFunction
import AFTD.Kb.Tcs.SimpleGraphDominatingSets

/-!
# dominating_occupancy_one_eq_avg_dominating_order_div_card

Topic: graphs   Node: d2d46e9b948f

Provenance: helper lemma. step towards weighted_dominating_occupancy_at_one_le_two_thirds

At activity lam = 1, the dominating occupancy equals the average dominating set order divided by the number of vertices.
-/

open Classical in
/-- At activity lam = 1, the dominating occupancy equals the average dominating set order divided by the number of vertices. -/
theorem dominating_occupancy_one_eq_avg_dominating_order_div_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    dominating_occupancy G 1 = (simple_graph_avg_dominating_order G : ℝ) / Fintype.card V := by
  rw [dominating_occupancy, simple_graph_avg_dominating_order, dominating_partition_function]
  simp only [one_pow, mul_one, Finset.sum_const, nsmul_eq_mul]
  push_cast
  rw [div_div]
  ring_nf
