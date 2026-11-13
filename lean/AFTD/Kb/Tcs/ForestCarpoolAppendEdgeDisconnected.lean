import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolForestEdgeSequence
import AFTD.Kb.Tcs.ValidCarpoolEdgeSequence

/-!
# forest_carpool_append_edge_disconnected

Topic: online_algorithms   Node: 5c4cb8661424

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

When a new edge appended to an edge sequence still forms a forest with no duplicate undirected edges, its endpoints lie in distinct components of the preceding graph.
-/

theorem forest_carpool_append_edge_disconnected (n : ℕ)
    (edges : List (Fin n × Fin n)) (u v : Fin n)
    (hf : CarpoolForestEdgeSequence n (edges ++ [(u, v)])) :
  ¬ (SimpleGraph.fromEdgeSet {s(e.1, e.2) | e ∈ edges}).Reachable u v := by
  obtain ⟨hval, hnd, hac⟩ := hf
  have huv : u ≠ v := hval (u, v) (by simp)
  have hnot : ∀ e ∈ edges, s(e.1, e.2) ≠ s(u, v) := by
    intro e he heq
    rw [List.map_append, List.nodup_append] at hnd
    exact hnd.2.2 _ (List.mem_map.mpr ⟨e, he, rfl⟩) _ (by simp) heq
  set H := SimpleGraph.fromEdgeSet {s(e.1, e.2) | e ∈ edges ++ [(u, v)]}
  have hedge : s(u, v) ∈ H.edgeSet := by
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨(u, v), by simp, rfl⟩, huv⟩
  have hb := (SimpleGraph.isAcyclic_iff_forall_isBridge.mp hac) hedge
  rw [SimpleGraph.isBridge_iff] at hb
  intro hr
  apply hb
  refine hr.mono ?_
  intro x y hxy
  rw [SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨⟨e, he, hex⟩, hne⟩ := hxy
  rw [SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj]
  refine ⟨⟨⟨e, List.mem_append_left _ he, hex⟩, hne⟩, ?_⟩
  simp only [Set.mem_singleton_iff]
  rw [← hex]
  exact hnot e he
