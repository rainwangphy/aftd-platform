import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsSubgraphOf

/-!
# digraph_subgraph_fintype_card_le

Topic: graphs   Node: 76c463e95b9d

Provenance: helper lemma. folklore

If a finite directed graph G is a subgraph of a finite directed graph H, then the vertex count of G is at most the vertex count of H.
-/

/-- If G is a subgraph of H, then the number of vertices of G is at most that of H. -/
theorem digraph_subgraph_fintype_card_le {V W : Type*} [Fintype V] [Fintype W] {G : Digraph V} {H : Digraph W} (h : digraph_is_subgraph_of G H) : Fintype.card V ≤ Fintype.card W := by
  rcases h with ⟨f, hf, -⟩
  exact Fintype.card_le_of_injective f hf
