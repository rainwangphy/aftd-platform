import AFTD.Prelude

/-!
# simple_graph_j_ef

Topic: combinatorics   Node: 60a67cd99326

Provenance: formalization of a published result. Source: arXiv:2610.36749, Section 1

The number of connected spanning subgraphs j_{ef}(G) of a finite simple graph G containing two given edges e and f.
-/

/-- The number of connected spanning subgraphs of a finite simple graph containing two edges e and f. -/
noncomputable def simple_graph_j_ef {V : Type*} [Fintype V] (G : SimpleGraph V) (e f : Sym2 V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun C : Finset (Sym2 V) =>
    (C : Set (Sym2 V)) ⊆ G.edgeSet ∧ e ∈ C ∧ f ∈ C ∧
      (SimpleGraph.fromEdgeSet (C : Set (Sym2 V))).Connected)).card
