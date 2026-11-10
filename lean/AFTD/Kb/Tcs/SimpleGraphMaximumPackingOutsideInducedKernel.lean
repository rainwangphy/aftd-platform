import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphMaximumPackingOutsideTrianglesInsideSupport

/-!
# simple_graph_maximum_packing_outside_induced_kernel

Topic: graphs   Node: 23ec6170e8f5

Provenance: helper lemma. Proposed bounded induced model for outside links in state/campaigns/triangle_reductions/outside_induced_kernel_in701.md; no novelty claim.

The support of a maximum packing plus one vertex has at most three times the packing size plus one vertices and contains every triangle through any of its vertices outside any maximum packing supported within it.
-/

theorem simple_graph_maximum_packing_outside_induced_kernel (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hmax : P.card = simple_graph_triangle_packing_number G) (x : Fin n) : (insert x (P.biUnion id)).card ≤ 3 * P.card + 1 ∧ ∀ (Q : Finset (Finset (Fin n))), (∀ t ∈ Q, G.IsNClique 3 t) → (Q : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1) → Q.card = P.card → Q.biUnion id ⊆ insert x (P.biUnion id) → ∀ y ∈ insert x (P.biUnion id), y ∉ Q.biUnion id → ∀ t : Finset (Fin n), G.IsNClique 3 t → y ∈ t → t ⊆ insert x (P.biUnion id) := by
  classical
  constructor
  · have h := Finset.card_biUnion_le_card_mul P id 3 (fun t ht => (htri t ht).card_eq.le)
    have h' := Finset.card_insert_le x (P.biUnion id)
    omega
  · intro Q hQtri hQdisj hQcard hQsub y hy hynot t ht hyt
    have hQmax : Q.card = simple_graph_triangle_packing_number G := hQcard.trans hmax
    have hsub := simple_graph_maximum_packing_outside_triangles_inside_support n G Q hQtri hQdisj hQmax y hynot t ht hyt
    exact hsub.trans (Finset.insert_subset_iff.mpr ⟨hy,hQsub⟩)
