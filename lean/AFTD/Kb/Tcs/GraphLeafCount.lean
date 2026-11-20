import AFTD.Prelude

/-!
# graph_leaf_count

Topic: graphs   Node: aa2438f62dd4

Provenance: formalization of a published result. Source: arXiv:2611.19473, Section 2

The number of leaves of a simple graph on a finite vertex type is the number of vertices with degree 1.
-/

open Classical in
/-- The number of leaves (vertices of degree 1) in a finite simple graph. -/
noncomputable def graph_leaf_count {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => H.degree v = 1)).card
