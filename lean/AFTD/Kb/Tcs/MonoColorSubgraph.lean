import AFTD.Prelude

/-!
# mono_color_subgraph

Topic: graphs   Node: 3b36859877ec

Provenance: formalization of a published result. Source: arXiv:2610.29813

For a simple graph G and an edge colouring c with colours in C, the monochromatic subgraph mono_color_subgraph G c col is the spanning subgraph of G whose edges are all edges of G assigned colour col.
-/

/-- The monochromatic subgraph of G in colour col under edge colouring c. -/
def mono_color_subgraph {V C : Type*} (G : SimpleGraph V) (c : G.edgeSet → C) (col : C) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, c ⟨e, h⟩ = col}
