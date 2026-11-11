import AFTD.Prelude

/-!
# color_avoiding_subgraph

Topic: combinatorics   Node: 3d57a3c1151e

Provenance: formalization of a published result. Source: arXiv:2611.11187, Section 2.1

For a simple graph G and an edge colouring c with colours in C, the j-avoiding subgraph color_avoiding_subgraph G c j is the spanning subgraph of G whose edges are all edges of G not assigned colour j.
-/

/-- The j-avoiding subgraph of G under an edge colouring c, formed by edges not of colour j. -/
def color_avoiding_subgraph {V C : Type*} (G : SimpleGraph V) (c : G.edgeSet → C) (j : C) : SimpleGraph V := SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, c ⟨e, h⟩ ≠ j}
