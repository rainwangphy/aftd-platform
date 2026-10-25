import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRichWitnessGraph
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# simple_graph_rich_witness_graph_coloring_iff

Topic: graphs   Node: c23427fabec9

Provenance: formalization of a published result. Source: arXiv:2610.16446, Section 2, Lemma 3 and its direct converse, in the simple-graph specialization.

Colorability of the prescribed-witness graph is equivalent to a proper edge-coloring of G in which every prescribed edge of R is rich.
-/

theorem simple_graph_rich_witness_graph_coloring_iff
    {V α : Type*} (G : SimpleGraph V) (R : Set G.edgeSet) :
    Nonempty ((simple_graph_rich_witness_graph G R).Coloring α) ↔
      ∃ c : G.lineGraph.Coloring α, ∀ r ∈ R, simple_graph_edge_is_rich G c r := by
  constructor
  · rintro ⟨c⟩
    let c' : G.lineGraph.Coloring α :=
      { toFun := c, map_rel' := fun h => c.valid ⟨h.ne, Or.inl h⟩ }
    refine ⟨c', ?_⟩
    intro r hr e f he hf hne
    exact c.valid ⟨hne, Or.inr ⟨r, hr, he, hf⟩⟩
  · rintro ⟨c, hc⟩
    refine ⟨{ toFun := c, map_rel' := ?_ }⟩
    intro e f h
    rcases h.2 with h' | ⟨r, hr, he, hf⟩
    · exact c.valid h'
    · exact hc r hr e f he hf h.1
