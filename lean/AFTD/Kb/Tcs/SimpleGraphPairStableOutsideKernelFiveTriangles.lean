import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphMaximumPackingOutsideTrianglesInsideSupport
import AFTD.Kb.Tcs.SimpleGraphPairStableActiveVertexAtLeastFiveTriangles
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_pair_stable_outside_kernel_five_triangles

Topic: graphs   Node: 7ed03c81854c

Provenance: helper lemma. Outside-link finite model in state/campaigns/triangle_reductions/outside_induced_kernel_in701.md; no novelty claim.

In a two-edge-stable graph, every active vertex that lies in the support-plus-one-vertex kernel and outside a maximum packing supported in that kernel has five distinct incident triangles inside the kernel.
-/

open scoped Sym2

theorem simple_graph_pair_stable_outside_kernel_five_triangles (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Finset (Fin n))) (hPmax : P.card = simple_graph_triangle_packing_number G)
    (hQ : ∀ t ∈ Q, G.IsNClique 3 t)
    (hQdisj : (Q : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hQcard : Q.card = P.card) (x : Fin n) (hQsub : Q.biUnion id ⊆ insert x (P.biUnion id))
    (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
       simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G)
    (y : Fin n) (hy : y ∈ insert x (P.biUnion id)) (hynot : y ∉ Q.biUnion id)
    (hactive : ∃ t : Finset (Fin n), G.IsNClique 3 t ∧ y ∈ t) :
    ∃ T : Finset (Finset (Fin n)), 5 ≤ T.card ∧
      ∀ t ∈ T, G.IsNClique 3 t ∧ y ∈ t ∧ t ⊆ insert x (P.biUnion id) := by
  classical
  let T := (Finset.univ : Finset (Finset (Fin n))).filter (fun t => G.IsNClique 3 t ∧ y ∈ t)
  have hfive : 5 ≤ T.card := simple_graph_pair_stable_active_vertex_at_least_five_triangles n G y hstable hactive
  refine ⟨T,hfive,?_⟩
  intro t ht
  have ht' := (Finset.mem_filter.mp ht).2
  have hQmax : Q.card = simple_graph_triangle_packing_number G := hQcard.trans hPmax
  have hsub := simple_graph_maximum_packing_outside_triangles_inside_support n G Q hQ hQdisj hQmax y hynot t ht'.1 ht'.2
  exact ⟨ht'.1,ht'.2,hsub.trans (Finset.insert_subset_iff.mpr ⟨hy,hQsub⟩)⟩
