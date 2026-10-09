import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSetsContaining

/-!
# simple_graph_local_avg_dominating_order_complete_four

Topic: graphs   Node: 796f08301a35

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.11446 (On the local average order of dominating sets). Sec. 1 gives avd_v(K_n) = (n+1)/2.

In K₄, the dominating sets containing a fixed vertex have average size 5/2 = (4+1)/2.
-/

theorem simple_graph_local_avg_dominating_order_complete_four :
    simple_graph_local_avg_dominating_order (⊤ : SimpleGraph (Fin 4)) 0 = 5 / 2 := by
  have h1 : (simple_graph_dominating_sets_containing (⊤ : SimpleGraph (Fin 4)) 0).card = 8 := by
    unfold simple_graph_dominating_sets_containing; decide
  have h2 : ∑ S ∈ simple_graph_dominating_sets_containing (⊤ : SimpleGraph (Fin 4)) 0,
      S.card = 20 := by
    unfold simple_graph_dominating_sets_containing; decide
  unfold simple_graph_local_avg_dominating_order
  rw [← Nat.cast_sum, h1, h2]; norm_num
