import AFTD.Prelude

/-!
# simple_graph_triangle_degree

Topic: graphs   Node: 1594e5dc55bd

Provenance: formalization of a published result. Source: arXiv:2610.08478 (Regular K_3-Irregular Graphs of Every Regularity at Least Nine), Abstract and Sec. 1 (triangle-degree, the K_3-degree of a vertex).

The triangle-degree td_G(v): the number of triangles of G containing v, i.e. the number of 2-element subsets {u, w} of the neighbourhood N(v) with u adjacent to w.
-/

/-- Triangle-degree of a vertex: the number of triangles of `G` through `v` (adjacent pairs inside the neighbourhood of `v`). -/
def simple_graph_triangle_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (((G.neighborFinset v).powersetCard 2).filter (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)).card
