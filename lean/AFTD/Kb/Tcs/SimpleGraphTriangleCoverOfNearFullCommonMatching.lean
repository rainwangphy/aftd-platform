import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphMaximumTrianglePackingEdgeMeets
import AFTD.Kb.Tcs.SimpleGraphMatchingLinkStarPacking
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingInsertSeparated
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverOfTwoStarPackings

/-!
# simple_graph_triangle_cover_of_near_full_common_matching

Topic: graphs   Node: 7f39e5b2c690

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign; related matching-cover reductions are in https://arxiv.org/abs/2610.15269, Lemma 2.3. Finite checks and limitations are recorded in state/campaigns/triangle_reductions/high_codegree_route_in512.md.

If an edge has a common-neighbor matching of size one below the graph triangle packing number and another common neighbor outside the matching, the triangle cover number is at most the packing number plus two.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_triangle_cover_of_near_full_common_matching
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (u v w : V) (M : Finset (Finset V))
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (hM : ∀ e ∈ M, e.card = 2 ∧ w ∉ e ∧
      (∀ x ∈ e, G.Adj u x ∧ G.Adj v x) ∧
      (∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y))
    (hdis : (M : Set (Finset V)).Pairwise Disjoint)
    (hnum : simple_graph_triangle_packing_number G = M.card + 1) :
    simple_graph_triangle_cover_number G ≤ M.card + 3 := by
  classical
  letI : Nonempty V := ⟨u⟩
  have huvne : u ≠ v := G.ne_of_adj huv
  have huwne : u ≠ w := G.ne_of_adj huw
  have hvwne : v ≠ w := G.ne_of_adj hvw
  have hrep : ∀ e ∈ M, ∃ a b : V, a ≠ b ∧ e = {a,b} := by
    intro e he
    exact Finset.card_eq_two.mp (hM e he).1
  choose! a b hab heq using hrep
  let C0 : Finset (Sym2 V) := M.image (fun e => s(a e,b e))
  let C : Finset (Sym2 V) := insert s(u,w) (insert s(v,w) C0)
  have hC0 : ∀ e ∈ C0, e ∈ G.edgeSet := by
    intro f hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    apply (hM e he).2.2.2 (a e) ?_ (b e) ?_ (hab e he)
    · have hmem : a e ∈ ({a e, b e} : Finset V) := by simp
      rw [← heq e he] at hmem
      exact hmem
    · have hmem : b e ∈ ({a e, b e} : Finset V) := by simp
      rw [← heq e he] at hmem
      exact hmem
  have hC : ∀ e ∈ C, e ∈ G.edgeSet := by
    intro f hf
    simp only [C, Finset.mem_insert] at hf
    rcases hf with rfl | rfl | hf
    · exact huw
    · exact hvw
    · exact hC0 f hf
  have hpair : ∀ e ∈ M, ∀ x ∈ e, ∀ y ∈ e, x ≠ y → s(x,y) ∈ C := by
    intro e he x hx y hy hxy
    have hx' : x = a e ∨ x = b e := by
      have hh : x ∈ ({a e,b e} : Finset V) := by rw [← heq e he]; exact hx
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
    have hy' : y = a e ∨ y = b e := by
      have hh : y ∈ ({a e,b e} : Finset V) := by rw [← heq e he]; exact hy
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
    have hmem : s(a e,b e) ∈ C0 := Finset.mem_image.mpr ⟨e, he, rfl⟩
    have hmemC : s(a e,b e) ∈ C := by simp [C, hmem]
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact (hxy rfl).elim
    · exact hmemC
    · simpa [Sym2.eq_swap] using hmemC
    · exact (hxy rfl).elim
  let P : Finset (Finset V) := M.image (fun e => insert u e)
  let Q : Finset (Finset V) := M.image (fun e => insert v e)
  let T : Finset V := {u,v,w}
  have hT : G.IsNClique 3 T := by
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro x hx y hy hxy
      simp only [T, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first | exact (hxy rfl).elim | exact huv | exact huv.symm | exact huw | exact huw.symm | exact hvw | exact hvw.symm
    · simp [T, huvne, huwne, hvwne, Ne.symm]
  have huM : ∀ e ∈ M, e.card = 2 ∧ (∀ x ∈ e, G.Adj u x) ∧
      (∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y) := by
    intro e he
    exact ⟨(hM e he).1, (fun x hx => ((hM e he).2.2.1 x hx).1), (hM e he).2.2.2⟩
  have hvM : ∀ e ∈ M, e.card = 2 ∧ (∀ x ∈ e, G.Adj v x) ∧
      (∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y) := by
    intro e he
    exact ⟨(hM e he).1, (fun x hx => ((hM e he).2.2.1 x hx).2), (hM e he).2.2.2⟩
  have huP := simple_graph_matching_link_star_packing G u M huM hdis
  have hvP := simple_graph_matching_link_star_packing G v M hvM hdis
  have huSep : ∀ s ∈ P, (s ∩ T).card ≤ 1 := by
    intro s hs
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
    have hvnot : v ∉ e := by
      intro hv
      exact G.irrefl (((hM e he).2.2.1 v hv).2)
    have hwnot : w ∉ e := (hM e he).2.1
    have hsub : insert u e ∩ T ⊆ {u} := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, T, Finset.mem_singleton] at hx
      simp only [Finset.mem_singleton]
      rcases hx with ⟨hxU, hxT⟩
      rcases hxU with rfl | hxE
      · rfl
      · rcases hxT with rfl | rfl | rfl
        · rfl
        · exact (hvnot hxE).elim
        · exact (hwnot hxE).elim
    exact (Finset.card_le_card hsub).trans (by simp)
  have hvSep : ∀ s ∈ Q, (s ∩ T).card ≤ 1 := by
    intro s hs
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
    have hunot : u ∉ e := by
      intro hu
      exact G.irrefl (((hM e he).2.2.1 u hu).1)
    have hwnot : w ∉ e := (hM e he).2.1
    have hsub : insert v e ∩ T ⊆ {v} := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, T, Finset.mem_singleton] at hx
      simp only [Finset.mem_singleton]
      rcases hx with ⟨hxV, hxT⟩
      rcases hxV with rfl | hxE
      · rfl
      · rcases hxT with rfl | rfl | rfl
        · exact (hunot hxE).elim
        · rfl
        · exact (hwnot hxE).elim
    exact (Finset.card_le_card hsub).trans (by simp)
  have huP' := simple_graph_triangle_packing_insert_separated G P T huP.1 huP.2.1 hT huSep
  have hvP' := simple_graph_triangle_packing_insert_separated G Q T hvP.1 hvP.2.1 hT hvSep
  have huMax := simple_graph_maximum_triangle_packing_edge_meets G _ huP'.1 huP'.2.1
    (by rw [huP'.2.2, huP.2.2, hnum])
  have hvMax := simple_graph_maximum_triangle_packing_edge_meets G _ hvP'.1 hvP'.2.1
    (by rw [hvP'.2.2, hvP.2.2, hnum])
  have hstar : ∀ z : V, ∀ s ∈ M.image (fun e => insert z e),
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → x = z ∨ y = z ∨ s(x,y) ∈ C := by
    intro z s hs x hx y hy hxy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
    simp only [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · rcases hy with rfl | hy
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (hpair e he x hx y hy hxy))
  have huStar : ∀ s ∈ insert T P, ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      x = u ∨ y = u ∨ s(x,y) ∈ C := by
    intro s hs x hx y hy hxy
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first
        | exact (hxy rfl).elim
        | exact Or.inl rfl
        | exact Or.inr (Or.inl rfl)
        | exact Or.inr (Or.inr (by simp [C, Sym2.eq_swap]))
    · exact hstar u s hs x hx y hy hxy
  have hvStar : ∀ s ∈ insert T Q, ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      x = v ∨ y = v ∨ s(x,y) ∈ C := by
    intro s hs x hx y hy hxy
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first
        | exact (hxy rfl).elim
        | exact Or.inl rfl
        | exact Or.inr (Or.inl rfl)
        | exact Or.inr (Or.inr (by simp [C, Sym2.eq_swap]))
    · exact hstar v s hs x hx y hy hxy
  have hc := simple_graph_triangle_cover_of_two_star_packings G u v _ _ C huv hC
    huMax hvMax huStar hvStar
  have hC0card : C0.card ≤ M.card := Finset.card_image_le
  have hCcard : C.card ≤ C0.card + 2 := by
    have h1 := Finset.card_insert_le s(v,w) C0
    have h2 := Finset.card_insert_le s(u,w) (insert s(v,w) C0)
    change C.card ≤ _ at h2
    omega
  omega
