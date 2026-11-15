import AFTD.Prelude

/-!
# mst_weight

Topic: graphs   Node: 1fb2db4788de

Provenance: formalization of a published result. Source: arXiv:2611.14755, Section 2

The minimum spanning tree weight of a finite edge-weighted simple graph (G, w) is the infimum over all spanning trees T ≤ G of the sum of the weights of the edges of T.
-/

/-- The weight of a minimum spanning tree in a finite edge-weighted graph (G, w). -/
noncomputable def mst_weight {V : Type*} [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℝ) : ℝ :=
  open scoped Classical in
  sInf { ∑ e ∈ T.edgeFinset, w e | (T : SimpleGraph V) (_ : T ≤ G) (_ : T.IsTree) }
