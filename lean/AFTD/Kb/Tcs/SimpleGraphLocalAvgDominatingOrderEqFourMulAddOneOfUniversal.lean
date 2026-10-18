import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrderGe
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrderStemLeOfCardTwo
import AFTD.Kb.Tcs.SimpleGraphLeafNeighborCount
import AFTD.Kb.Tcs.SimpleGraphIsStarLike
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrder

/-!
# simple_graph_local_avg_dominating_order_eq_four_mul_add_one_of_universal

Topic: graphs   Node: 264b159d0026

Provenance: helper lemma. step towards simple_graph_local_avg_dominating_order_stem_le

Rigidity in the universal-vertex regime: if G has no isolated vertices, v is adjacent to every other vertex (deg v = n − 1), and avd_v(G) = (4n+1)/6, then v has exactly one leaf neighbour and G is star-like. (In fact n = 2 and G is K2.)
-/

/-- If v is adjacent to every other vertex, equality in (4n+1)/6 forces n = 2, hence K2, hence one leaf neighbour and star-like: the rigidity half of the characterisation in the universal-vertex regime (where the extremal m·K2 family lives). -/
theorem simple_graph_local_avg_dominating_order_eq_four_mul_add_one_of_universal
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hiso : ∀ w, 0 < G.degree w) (v : V) (hdeg : G.degree v = Fintype.card V - 1)
    (heq : simple_graph_local_avg_dominating_order G v = (4 * (Fintype.card V : ℚ) + 1) / 6) :
    simple_graph_leaf_neighbor_count G v = 1 ∧ simple_graph_is_star_like G := by
  have h1 := (simple_graph_local_avg_dominating_order_ge (G := G) v).2.mpr hdeg
  rw [h1] at heq
  have hc : (Fintype.card V : ℚ) = 2 := by linarith
  have hcard : Fintype.card V = 2 := by exact_mod_cast hc
  exact (simple_graph_local_avg_dominating_order_stem_le_of_card_two G hcard hiso v).2
