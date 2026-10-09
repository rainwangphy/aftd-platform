import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSetsContaining

/-!
# simple_graph_local_avg_dominating_order_bot_three

Topic: graphs   Node: 28bcdaca84ca

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.11446 (On the local average order of dominating sets). Sec. 1 gives avd_v of the empty graph = n.

In the edgeless graph on 3 vertices, the only dominating set is the whole vertex set, so avd_v = 3.
-/

theorem simple_graph_local_avg_dominating_order_bot_three :
    simple_graph_local_avg_dominating_order (⊥ : SimpleGraph (Fin 3)) 0 = 3 := by
  have h1 : (simple_graph_dominating_sets_containing (⊥ : SimpleGraph (Fin 3)) 0).card = 1 := by
    unfold simple_graph_dominating_sets_containing; decide
  have h2 : ∑ S ∈ simple_graph_dominating_sets_containing (⊥ : SimpleGraph (Fin 3)) 0,
      S.card = 3 := by
    unfold simple_graph_dominating_sets_containing; decide
  unfold simple_graph_local_avg_dominating_order
  rw [← Nat.cast_sum, h1, h2]; norm_num
