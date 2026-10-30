import AFTD.Prelude

/-!
# edge_list_h_colorable

Topic: np_completeness   Node: eb411d316c0f

Provenance: formalization of a published result. Source: arXiv:2610.35794 (Computational complexity of the H-coloring problem in cubic graphs), Sec. 1: an H-coloring of a cubic graph G is f : E(G) → E(H) with f(∂_G(v)) = ∂_H(x) for some x, for every vertex v (here H a simple graph, G an edge-list multigraph)

With W : Type implicit, takes, in this order, H : SimpleGraph W, n : ℕ and an edge list es : List (ℕ × ℕ) (edge i : Fin es.length joins es[i].1 and es[i].2), and says the multigraph es on the vertices v < n has an H-coloring: there is f : Fin es.length → H.edgeSet such that for every v : ℕ with v < n there is x : W with the image under (fun i => (f i : Sym2 W)) of the set {i | es[i].1 = v ∨ es[i].2 = v} equal to H.incidenceSet x.
-/

/-- An edge-list multigraph has an H-coloring: edges map to edges of H, each vertex star onto a vertex star of H. -/
def edge_list_h_colorable {W : Type} (H : SimpleGraph W) (n : ℕ) (es : List (ℕ × ℕ)) : Prop :=
  ∃ f : Fin es.length → H.edgeSet, ∀ v : ℕ, v < n → ∃ x : W,
    (fun i => (f i : Sym2 W)) '' {i | es[i].1 = v ∨ es[i].2 = v} = H.incidenceSet x
