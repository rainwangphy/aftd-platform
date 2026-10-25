import AFTD.Prelude
import AFTD.Kb.Tcs.MaxDegreeInduceV3LeTwoIff
import AFTD.Kb.Tcs.SimpleGraphV3

/-!
# maxDegree_induce_V3_le_two_iff_neighbor_filter

Topic: graphs   Node: 2387555aa5d9

Provenance: helper lemma. step towards subcubic_maxDegree_induce_V3_le_two_exists_rich_neighbor_five_coloring

For any finite simple graph G, the induced subgraph on the vertices of degree 3 has maximum degree at most 2 if and only if every degree-3 vertex has at most two neighbours of degree 3.
-/

/-- The induced subgraph on the degree-3 vertices has maximum degree at most 2 if and only if each degree-3 vertex in G has at most two degree-3 neighbours. -/
theorem maxDegree_induce_V3_le_two_iff_neighbor_filter {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.induce (simple_graph_V3 G : Set V)).maxDegree ≤ 2 ↔
      ∀ v, G.degree v = 3 → ((G.neighborFinset v).filter (fun w => G.degree w = 3)).card ≤ 2 := by
  rw [maxDegree_induce_V3_le_two_iff]
  have key : ∀ (v : (simple_graph_V3 G : Set V)),
      (G.induce (simple_graph_V3 G : Set V)).degree v =
      ((G.neighborFinset v.val).filter (fun w => G.degree w = 3)).card := by
    intro v
    rw [SimpleGraph.degree]
    refine Finset.card_bij (fun (w : (simple_graph_V3 G : Set V)) _ => w.val) ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨(SimpleGraph.mem_neighborFinset _ _ _).mp (by simpa using ha),
        by simpa [simple_graph_V3] using a.property⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      exact Subtype.ext heq
    · intro b hb
      rw [Finset.mem_filter] at hb
      refine ⟨⟨b, by simpa [simple_graph_V3] using hb.2⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]
      exact (SimpleGraph.mem_neighborFinset _ _ _).mp hb.1
  constructor
  · intro h v hv
    have hv' : v ∈ (simple_graph_V3 G : Set V) := by
      simp [simple_graph_V3, hv]
    have := h ⟨v, hv'⟩
    rwa [key] at this
  · intro h v
    rw [key v]
    exact h v.val (by simpa [simple_graph_V3] using v.property)
