import AFTD.Prelude

/-!
# simple_graph_triangle_cover_number

Topic: graphs   Node: 01986931fefd

Provenance: formalization of a published result. Source: arXiv:2610.15539 (Tuza's conjecture under an edge-count condition), Sec. 1 (τ(G), the triangle cover number).

τ(G): the minimum number of edges of G such that every triangle of G contains one of them.
-/

/-- `τ(G)`: the minimum number of edges of `G` meeting every triangle of `G`. -/
noncomputable def simple_graph_triangle_cover_number {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ G.edgeSet) ∧
    (∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ F, ∀ x ∈ e, x ∈ t) ∧ F.card = n}
