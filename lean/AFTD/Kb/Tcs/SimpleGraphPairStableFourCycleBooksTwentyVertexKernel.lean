import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphPairStableActiveVertexAtLeastFiveTriangles
import AFTD.Kb.Tcs.SimpleGraphPairStableTwoDisjointBooksSixVertexKernel

/-!
# simple_graph_pair_stable_four_cycle_books_twenty_vertex_kernel

Topic: graphs   Node: af0aefbf8809

Provenance: helper lemma. Pair-deletion preserving representative kernel for four cycle-edge books in the triangle-packing campaign.

If every triangle of a two-edge-stable finite graph is either inside S or has one outside vertex and an edge of a four-cycle on S, at most twenty outside vertices can be retained so the induced graph has the same triangle-packing number and remains two-edge-stable.
-/

open scoped Sym2

lemma simple_graph_pair_stable_four_cycle_books_twenty_vertex_kernel_no_outside_triangle
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) (a b c d : Fin n)
    (hS : ({a,b,c,d} : Finset (Fin n)) ⊆ S)
    (hclass : ∀ t : Finset (Fin n), G.IsNClique 3 t → t ⊆ S ∨ ∃ w, w ∉ S ∧ (t = {a,c,w} ∨ t = {a,d,w} ∨ t = {b,c,w} ∨ t = {b,d,w}))
    (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
      simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G)
    (w : Fin n) (hw : w ∉ S) :
    ¬ ∃ t : Finset (Fin n), G.IsNClique 3 t ∧ w ∈ t := by
  intro ⟨t, ht, hwt⟩
  have ha : a ∈ S := hS (by simp)
  have hb : b ∈ S := hS (by simp)
  have hc : c ∈ S := hS (by simp)
  have hd : d ∈ S := hS (by simp)
  have h5 := simple_graph_pair_stable_active_vertex_at_least_five_triangles n G w hstable ⟨t, ht, hwt⟩
  have ⟨s, hs5, hs_mem⟩ : ∃ s : Finset (Finset (Fin n)), 5 ≤ s.card ∧ ∀ u, u ∈ s ↔ G.IsNClique 3 u ∧ w ∈ u := by
    refine ⟨_, h5, ?_⟩
    intro u; simp
  let cand : Finset (Finset (Fin n)) := {{a,c,w}, {a,d,w}, {b,c,w}, {b,d,w}}
  have hcand_card : cand.card ≤ 4 := by
    apply le_trans (Finset.card_insert_le _ _)
    apply Nat.succ_le_succ
    apply le_trans (Finset.card_insert_le _ _)
    apply Nat.succ_le_succ
    apply le_trans (Finset.card_insert_le _ _)
    apply Nat.succ_le_succ
    rw [Finset.card_singleton]
  have hsub : s ⊆ cand := by
    intro u hu
    rw [hs_mem] at hu
    rcases hu with ⟨hu_cl, hu_w⟩
    rcases hclass u hu_cl with huS | ⟨w', hw', hu_cases⟩
    · exfalso; exact hw (huS hu_w)
    · rcases hu_cases with rfl | rfl | rfl | rfl
      · have : w = w' := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu_w
          rcases hu_w with rfl | rfl | rfl
          · exfalso; exact hw ha
          · exfalso; exact hw hc
          · rfl
        subst this
        simp [cand]
      · have : w = w' := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu_w
          rcases hu_w with rfl | rfl | rfl
          · exfalso; exact hw ha
          · exfalso; exact hw hd
          · rfl
        subst this
        simp [cand]
      · have : w = w' := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu_w
          rcases hu_w with rfl | rfl | rfl
          · exfalso; exact hw hb
          · exfalso; exact hw hc
          · rfl
        subst this
        simp [cand]
      · have : w = w' := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu_w
          rcases hu_w with rfl | rfl | rfl
          · exfalso; exact hw hb
          · exfalso; exact hw hd
          · rfl
        subst this
        simp [cand]
  have hcard_le := Finset.card_le_card hsub
  omega

theorem simple_graph_pair_stable_four_cycle_books_twenty_vertex_kernel (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) (a b c d : Fin n) (habcd : ({a,b,c,d} : Finset (Fin n)).card = 4) (hS : ({a,b,c,d} : Finset (Fin n)) ⊆ S) (hclass : ∀ t : Finset (Fin n), G.IsNClique 3 t → t ⊆ S ∨ ∃ w, w ∉ S ∧ (t = {a,c,w} ∨ t = {a,d,w} ∨ t = {b,c,w} ∨ t = {b,d,w})) (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f → simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G) : ∃ U : Finset (Fin n), Disjoint U S ∧ U.card ≤ 20 ∧ let H := G.induce (↑(S ∪ U) : Set (Fin n)); simple_graph_triangle_packing_number H = simple_graph_triangle_packing_number G ∧ ∀ e f : Sym2 {v : Fin n // v ∈ S ∪ U}, e ∈ H.edgeSet → f ∈ H.edgeSet → e ≠ f → simple_graph_triangle_packing_number (H.deleteEdges {e,f}) = simple_graph_triangle_packing_number H := by
  have hall : ∀ t : Finset (Fin n), G.IsNClique 3 t → t ⊆ S := by
    intro t ht
    rcases hclass t ht with htS | ⟨w, hw, hw_or⟩
    · exact htS
    · exfalso
      have hwt : w ∈ t := by rcases hw_or with rfl | rfl | rfl | rfl <;> simp
      exact simple_graph_pair_stable_four_cycle_books_twenty_vertex_kernel_no_outside_triangle
        n G S a b c d hS hclass hstable w hw ⟨t, ht, hwt⟩
  refine ⟨∅, Finset.disjoint_empty_left S, by simp, ?_⟩
  dsimp
  have hSU : (S ∪ ∅ : Finset (Fin n)) = S := Finset.union_empty S
  have hSU_coe : (↑(S ∪ (∅ : Finset (Fin n))) : Set (Fin n)) = (↑S : Set (Fin n)) := by rw [hSU]
  have h_H_pack : simple_graph_triangle_packing_number (G.induce (↑(S ∪ ∅) : Set (Fin n))) =
      simple_graph_triangle_packing_number G := by
    rw [hSU_coe]
    exact simple_graph_pair_stable_two_disjoint_books_six_vertex_kernel_packing_num_induce_eq n G S hall
  refine ⟨h_H_pack, ?_⟩
  intro e f he hf hne
  have he_G : Sym2.map Subtype.val e ∈ G.edgeSet := by
    induction' e using Sym2.inductionOn with u v
    simp only [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] at he
    rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
    exact he
  have hf_G : Sym2.map Subtype.val f ∈ G.edgeSet := by
    induction' f using Sym2.inductionOn with u v
    simp only [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] at hf
    rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
    exact hf
  have hne_G : Sym2.map Subtype.val e ≠ Sym2.map Subtype.val f :=
    (Sym2.map.injective Subtype.val_injective).ne hne
  have h_del_pack := hstable (Sym2.map Subtype.val e) (Sym2.map Subtype.val f) he_G hf_G hne_G
  have hall_del : ∀ t, (G.deleteEdges {Sym2.map Subtype.val e, Sym2.map Subtype.val f}).IsNClique 3 t →
      t ⊆ (S ∪ ∅ : Finset (Fin n)) := by
    intro t ht
    rw [hSU]
    exact hall t (SimpleGraph.IsNClique.mono (SimpleGraph.deleteEdges_le _) ht)
  have h_ind_eq := simple_graph_pair_stable_two_disjoint_books_six_vertex_kernel_packing_num_induce_eq
    n (G.deleteEdges {Sym2.map Subtype.val e, Sym2.map Subtype.val f}) (S ∪ ∅) hall_del
  rw [simple_graph_pair_stable_two_disjoint_books_six_vertex_kernel_induce_deleteEdges]
  exact h_ind_eq.trans (h_del_pack.trans h_H_pack.symm)
