import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphPairStableVertexLinkEdgeSpokeExchange
import AFTD.Kb.Tcs.SimpleGraphMaximumPackingOutsideTrianglesInsideSupport

/-!
# simple_graph_pair_stable_kernel_link_edge_spoke_exchange

Topic: graphs   Node: ea3a6a5470eb

Provenance: helper lemma. Exact local link transfer for the induced model in state/campaigns/triangle_reductions/outside_induced_kernel_in701.md; no novelty claim.

For an active outside vertex of a maximum packing supported in a support-plus-one-vertex kernel, the local edge/spoke exchange guaranteed by global two-edge stability has its witness vertices inside the kernel.
-/

open scoped Sym2

theorem simple_graph_pair_stable_kernel_link_edge_spoke_exchange (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Finset (Fin n))) (hPmax : P.card = simple_graph_triangle_packing_number G)
    (hQ : ∀ t ∈ Q, G.IsNClique 3 t)
    (hQdisj : (Q : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hQcard : Q.card = P.card) (x : Fin n) (hQsub : Q.biUnion id ⊆ insert x (P.biUnion id))
    (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
       simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G)
    (y : Fin n) (hy : y ∈ insert x (P.biUnion id)) (hynot : y ∉ Q.biUnion id)
    (a b w : Fin n) (hya : G.Adj y a) (hyb : G.Adj y b) (hab : G.Adj a b) (hyw : G.Adj y w) :
    ∃ u v : Fin n, u ∈ insert x (P.biUnion id) ∧ v ∈ insert x (P.biUnion id) ∧
      G.Adj y u ∧ G.Adj y v ∧ G.Adj u v ∧
      (u = a ∨ u = b ∨ v = a ∨ v = b) ∧ u ≠ w ∧ v ≠ w ∧ s(u,v) ≠ s(a,b) := by
  classical
  obtain ⟨u,v,hyu,hyv,huv,hmeet,huw,hvw,hne⟩ :=
    simple_graph_pair_stable_vertex_link_edge_spoke_exchange n G y hstable a b w hya hyb hab hyw
  have hneq1 : y ≠ u := hyu.ne
  have hneq2 : y ≠ v := hyv.ne
  have hneq3 : u ≠ v := huv.ne
  have ht : G.IsNClique 3 ({y,u,v} : Finset (Fin n)) := by
    constructor
    · intro r hr s hs hrs
      simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hr hs
      rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl
      all_goals first | contradiction | assumption | exact SimpleGraph.Adj.symm (by assumption)
    · simp [hneq1,hneq2,hneq3]
  have hQmax : Q.card = simple_graph_triangle_packing_number G := hQcard.trans hPmax
  have hsub := simple_graph_maximum_packing_outside_triangles_inside_support n G Q hQ hQdisj hQmax y hynot {y,u,v} ht (by simp)
  have hsubW := hsub.trans (Finset.insert_subset_iff.mpr ⟨hy,hQsub⟩)
  exact ⟨u,v,hsubW (by simp),hsubW (by simp),hyu,hyv,huv,hmeet,huw,hvw,hne⟩
