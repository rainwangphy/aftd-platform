import AFTD.Prelude

/-!
# simple_graph_rich_witness_graph

Topic: graphs   Node: 3e3e0c8a23eb

Provenance: formalization of a published result. Source: arXiv:2610.16446, Section 2, the calligraphic graph defined before Lemma 3; simple-graph specialization, used for OP-309.

The graph on the edges of G joining adjacent edges and distinct pairs sharing a neighboring edge from R.
-/

def simple_graph_rich_witness_graph {V : Type*} (G : SimpleGraph V)
    (R : Set G.edgeSet) : SimpleGraph G.edgeSet where
  Adj e f := e ≠ f ∧ (G.lineGraph.Adj e f ∨
    ∃ r ∈ R, G.lineGraph.Adj r e ∧ G.lineGraph.Adj r f)
  symm := ⟨by
    intro e f h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | ⟨r, hr, he, hf⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨r, hr, hf, he⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩
