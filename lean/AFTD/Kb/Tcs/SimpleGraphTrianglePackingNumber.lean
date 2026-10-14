import AFTD.Prelude

/-!
# simple_graph_triangle_packing_number

Topic: graphs   Node: 5d2711f99e19

Provenance: formalization of a published result. Source: arXiv:2610.15539 (Tuza's conjecture under an edge-count condition), Sec. 1 (ν(G), the triangle packing number).

ν(G): the maximum number of pairwise edge-disjoint triangles of G (two triangles are edge-disjoint when they share at most one vertex).
-/

/-- `ν(G)`: the maximum number of pairwise edge-disjoint triangles of `G`. -/
noncomputable def simple_graph_triangle_packing_number {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sSup {n | ∃ T : Finset (Finset V), (∀ t ∈ T, G.IsNClique 3 t) ∧
    (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T.card = n}
