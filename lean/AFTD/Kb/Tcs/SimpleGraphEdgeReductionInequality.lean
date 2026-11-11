import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberGeOfEdgeReduction
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberLeOfEdgeReduction
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_edge_reduction_inequality

Topic: graphs   Node: 1e3469c31519

Provenance: formalization of a published result. Source: arXiv:2611.11128 Lemma 2.2 -- Triangle-overlap cores and density bounds for Tuza's conjecture

Let G be a finite simple graph. Suppose there exist a nonempty edge set F ⊆ E(G), a set S of pairwise edge-disjoint triangles of G, and an edge set X ⊆ E(G) such that X meets every triangle of G containing an edge of F, E(S) \ F ⊆ X, and |X| ≤ 2|S|. Let G' = G \ (F ∪ X). Then ν(G') + |S| ≤ ν(G), τ(G) ≤ τ(G') + |X|, and τ(G) - 2ν(G) ≤ τ(G') - 2ν(G').
-/

open Classical in
/-- Edge-reduction inequality for triangle packing and covering (Lemma 2.2). -/
theorem simple_graph_edge_reduction_inequality
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) (hFne : F.Nonempty)
    (S : Finset (Finset V)) (hS : ∀ t ∈ S, G.IsNClique 3 t)
    (hSpairwise : (S : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1))
    (X : Finset (Sym2 V)) (hX : X ⊆ G.edgeFinset)
    (hXmeets : ∀ t : Finset V, G.IsNClique 3 t →
      (∃ e ∈ F, ∀ x ∈ e, x ∈ t) → ∃ e ∈ X, ∀ x ∈ e, x ∈ t)
    (hES : (S.biUnion finite_vertex_set_edge_encoding \ F) ⊆ X)
    (hXcard : X.card ≤ 2 * S.card) :
    let G' := G.deleteEdges (↑(F ∪ X) : Set (Sym2 V))
    simple_graph_triangle_packing_number G' + S.card ≤ simple_graph_triangle_packing_number G ∧
    simple_graph_triangle_cover_number G ≤ simple_graph_triangle_cover_number G' + X.card ∧
    simple_graph_triangle_cover_number G - 2 * simple_graph_triangle_packing_number G ≤
      simple_graph_triangle_cover_number G' - 2 * simple_graph_triangle_packing_number G' := by
  intro G'
  have h1 : simple_graph_triangle_packing_number G' + S.card ≤ simple_graph_triangle_packing_number G :=
    simple_graph_triangle_packing_number_ge_of_edge_reduction G F hF hFne S hS hSpairwise X hX hXmeets hES
  have h2 : simple_graph_triangle_cover_number G ≤ simple_graph_triangle_cover_number G' + X.card :=
    simple_graph_triangle_cover_number_le_of_edge_reduction G F hF hFne S hS hSpairwise X hX hXmeets hES
  refine ⟨h1, h2, ?_⟩
  dsimp [G'] at *
  omega
