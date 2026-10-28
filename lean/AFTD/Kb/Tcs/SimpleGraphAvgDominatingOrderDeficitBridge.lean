import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSets

/-!
# simple_graph_avg_dominating_order_deficit_bridge

Topic: graphs   Node: f583ef100c3d

Provenance: helper lemma. step towards dominating_average_star_like_vertex_stability

The dominating set order deficit 2n/3 - avd(G) can be rewritten as (2n|D(G)| - 3 ∑_{S∈D(G)} |S|) / (3|D(G)|).
-/

/-- The average dominating set order deficit 2n/3 - avd(G) expressed as an exact rational fraction over 3|D(G)|. -/
theorem simple_graph_avg_dominating_order_deficit_bridge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : 2 * (Fintype.card V : ℚ) / 3 - simple_graph_avg_dominating_order G = (2 * (Fintype.card V : ℚ) * (simple_graph_dominating_sets G).card - 3 * (∑ S ∈ simple_graph_dominating_sets G, (S.card : ℚ))) / (3 * (simple_graph_dominating_sets G).card) := by
  have hne : (simple_graph_dominating_sets G).Nonempty := ⟨Finset.univ, by
    rw [simple_graph_dominating_sets, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun w => Or.inl (Finset.mem_univ w)⟩⟩
  have hd : ((simple_graph_dominating_sets G).card : ℚ) ≠ 0 := by
    have : 0 < (simple_graph_dominating_sets G).card := Finset.card_pos.mpr hne
    positivity
  unfold simple_graph_avg_dominating_order
  field_simp
