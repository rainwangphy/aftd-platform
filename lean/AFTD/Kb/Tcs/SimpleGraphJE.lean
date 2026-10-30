import AFTD.Prelude

/-!
# simple_graph_j_e

Topic: combinatorics   Node: 4e9e0cd93ca5

Provenance: formalization of a published result. Source: arXiv:2610.36749, Section 1

The number of connected spanning subgraphs j_e(G) of a finite simple graph G containing a given edge e.
-/

/-- The number of connected spanning subgraphs of a finite simple graph containing an edge e. -/
noncomputable def simple_graph_j_e {V : Type*} [Fintype V] (G : SimpleGraph V) (e : Sym2 V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun C : Finset (Sym2 V) =>
    (C : Set (Sym2 V)) ⊆ G.edgeSet ∧ e ∈ C ∧
      (SimpleGraph.fromEdgeSet (C : Set (Sym2 V))).Connected)).card
