import AFTD.Prelude

/-!
# simple_graph_cut_rank

Topic: quantum_mechanics   Node: 7c698f7cf110

Provenance: formalization of a published result. Source: arXiv:2511.19585 Eq. (2.19)

For a finite type V with decidable equality, a simple graph G on V with decidable adjacency, and a finite subset X : Finset V, simple_graph_cut_rank G X is the rank over ZMod 2 of the submatrix of G.adjMatrix (ZMod 2) with rows indexed by X and columns indexed by the complement Xᶜ.
-/

/-- The rank over F₂ of the cut submatrix between X and V \ X. -/
noncomputable def simple_graph_cut_rank {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : ℕ := Matrix.rank ((G.adjMatrix (ZMod 2)).submatrix (Subtype.val : ↥X → V) (Subtype.val : ↥(Xᶜ) → V))
