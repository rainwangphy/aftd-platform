import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphMaximumTrianglePackingEdgeMeets

/-!
# simple_graph_maximum_packing_outside_triangles_inside_support

Topic: graphs   Node: a13d522a030e

Provenance: helper lemma. Elementary maximum-packing observation used in state/campaigns/triangle_reductions/outside_induced_kernel_in701.md; no novelty claim.

Every triangle through a vertex outside a maximum triangle packing lies in that vertex together with the packing support.
-/

theorem simple_graph_maximum_packing_outside_triangles_inside_support (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hmax : P.card = simple_graph_triangle_packing_number G) (x : Fin n) (hx : x ∉ P.biUnion id) (t : Finset (Fin n)) (ht : G.IsNClique 3 t) (hxt : x ∈ t) : t ⊆ insert x (P.biUnion id) := by
  classical
  obtain ⟨p,hp,hcount⟩ := simple_graph_maximum_triangle_packing_edge_meets G P htri hdisj hmax t ht
  have hxp : x ∉ p := by
    intro h
    apply hx
    exact Finset.mem_biUnion.mpr ⟨p,hp,h⟩
  have hsub : p ∩ t ⊆ t.erase x := by
    intro y hy
    have hy' := Finset.mem_inter.mp hy
    apply Finset.mem_erase.mpr
    exact ⟨by intro h; subst y; exact hxp hy'.1,hy'.2⟩
  have hcard : (t.erase x).card = 2 := by
    have h := Finset.card_erase_of_mem hxt
    rw [ht.card_eq] at h
    omega
  have heq : p ∩ t = t.erase x := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro y hy
  by_cases hxy : y = x
  · subst y; simp
  · apply Finset.mem_insert.mpr
    right
    have hy' : y ∈ p ∩ t := by rw [heq]; exact Finset.mem_erase.mpr ⟨hxy,hy⟩
    exact Finset.mem_biUnion.mpr ⟨p,hp,(Finset.mem_inter.mp hy').1⟩
