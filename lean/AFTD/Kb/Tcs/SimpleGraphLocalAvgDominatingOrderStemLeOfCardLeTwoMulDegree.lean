import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrderLeOfNoIsolated
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrder

/-!
# simple_graph_local_avg_dominating_order_stem_le_of_card_le_two_mul_degree

Topic: graphs   Node: e2d7e94773ea

Provenance: helper lemma. step towards simple_graph_local_avg_dominating_order_stem_le

If G has no isolated vertices and |V| ≤ 2 deg(v), then avd_v(G) ≤ (4|V|+1)/6. This is the large-degree regime of the target's inequality, where the known degree-sensitive bound already suffices.
-/

/-- In the regime n ≤ 2 deg v the already-proved (5n − 2 deg v + 1)/6 bound is at most (4n+1)/6, so the target's inequality holds there. -/
theorem simple_graph_local_avg_dominating_order_stem_le_of_card_le_two_mul_degree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hiso : ∀ w, 0 < G.degree w) (v : V) (hdeg : Fintype.card V ≤ 2 * G.degree v) :
    simple_graph_local_avg_dominating_order G v ≤ (4 * (Fintype.card V : ℚ) + 1) / 6 := by
  have h := simple_graph_local_avg_dominating_order_le_of_no_isolated G hiso v
  have h2 : (Fintype.card V : ℚ) ≤ 2 * (G.degree v : ℚ) := by exact_mod_cast hdeg
  linarith
