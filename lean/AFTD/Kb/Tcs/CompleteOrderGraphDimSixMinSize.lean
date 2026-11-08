import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteOrderGraphDimSixLowerBound
import AFTD.Kb.Tcs.CompleteOrderGraphDimSixUpperBound
import AFTD.Kb.Tcs.OrderGraph
import AFTD.Kb.Tcs.Order
import AFTD.Kb.Tcs.OrderGraphIsComplete

/-!
# complete_order_graph_dim_six_min_size

Topic: combinatorics   Node: ce96720134a0

Provenance: formalization of a published result. Source: arXiv:2610.39311 Corollary 8 -- Tight Asymptotic Bounds on the Size of Order Graphs

The minimum size of a complete order graph of dimension 6 is exactly 40: every complete order graph of dimension 6 has at least 40 edges, and there exists a complete order graph of dimension 6 with exactly 40 edges.
-/

/-- The minimum size of a complete order graph of dimension 6 is exactly 40 (arXiv:2610.39311 Corollary 8). -/
theorem complete_order_graph_dim_six_min_size :
    (∀ G : OrderGraph 6, order_graph_is_complete G → 40 ≤ G.E.card) ∧
    (∃ G : OrderGraph 6, order_graph_is_complete G ∧ G.E.card = 40) := ⟨complete_order_graph_dim_six_lower_bound, complete_order_graph_dim_six_upper_bound⟩
