import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSets

/-!
# simple_graph_avg_dominating_order_complete_two

Topic: graphs   Node: 20111df4cd5a

Provenance: helper lemma. step towards simple_graph_local_avg_dominating_order_stem_le

The global average order of dominating sets of K2 is 4/3 (the three dominating sets {0}, {1}, {0,1} have sizes 1, 1, 2). Note this is exactly 2n/3 at n = 2, i.e. the equality case of the Beaton--Cameron bound, and it is smaller than the local value avd_v(K2) = 3/2 banked in `simple_graph_local_avg_dominating_order_stem_le_of_card_two`.
-/

/-- Sanity value of the global average: on K2 the three dominating sets have sizes 1,1,2, so avd(K2) = 4/3 = 2·2/3. -/
theorem simple_graph_avg_dominating_order_complete_two :
    simple_graph_avg_dominating_order (⊤ : SimpleGraph (Fin 2)) = 4 / 3 := by
  have hs : simple_graph_dominating_sets (⊤ : SimpleGraph (Fin 2)) = {{0},{1},{0,1}} := by decide
  rw [simple_graph_avg_dominating_order, hs]
  have hsum : (∑ S ∈ ({{0},{1},{0,1}} : Finset (Finset (Fin 2))), S.card) = 4 := by decide
  have h1 : (∑ S ∈ ({{0},{1},{0,1}} : Finset (Finset (Fin 2))), (S.card : ℚ)) = 4 := by
    rw [← Nat.cast_sum, hsum]
    norm_num
  have h2 : ({{0},{1},{0,1}} : Finset (Finset (Fin 2))).card = 3 := by decide
  rw [h1, h2]
  norm_num
