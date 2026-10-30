import AFTD.Prelude

/-!
# simple_graph_j

Topic: combinatorics   Node: 23e090b75ef4

Provenance: formalization of a published result. Source: arXiv:2610.36749, Section 1

The number of connected spanning subgraphs j(G) of a finite simple graph G.
-/

/-- The number of connected spanning subgraphs of a finite simple graph. -/
noncomputable def simple_graph_j {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun C : Finset (Sym2 V) =>
    (C : Set (Sym2 V)) ⊆ G.edgeSet ∧
      (SimpleGraph.fromEdgeSet (C : Set (Sym2 V))).Connected)).card
