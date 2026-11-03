import AFTD.Prelude

/-!
# finset_rank_two_cover_matching_bound

Topic: graphs   Node: ebc72e2123d9

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign, related to matching-cover reductions in https://arxiv.org/abs/2610.15269; see state/campaigns/triangle_reductions/high_codegree_route_in512.md.

For any finite family of sets of size at most two, some pairwise-disjoint subfamily of two-element sets has size at least the size of the union minus the number of sets.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem finset_rank_two_cover_matching_bound {α : Type*} [DecidableEq α]
    (B : Finset (Finset α)) (hB : ∀ b ∈ B, b.card ≤ 2) :
    ∃ M : Finset (Finset α), M ⊆ B ∧
      (M : Set (Finset α)).Pairwise Disjoint ∧
      (∀ e ∈ M, e.card = 2) ∧
      (B.biUnion id).card ≤ B.card + M.card := by
  classical
  revert hB
  induction B using Finset.induction_on with
  | empty =>
      intro hB
      refine ⟨∅, by simp, by simp, by simp, ?_⟩
      simp
  | @insert b B hb ih =>
      intro hB
      have hbsize : b.card ≤ 2 := hB b (Finset.mem_insert_self _ _)
      have hB' : ∀ e ∈ B, e.card ≤ 2 := by
        intro e he
        exact hB e (Finset.mem_insert_of_mem he)
      obtain ⟨M, hMB, hMdis, hMtwo, hbound⟩ := ih hB'
      let U := B.biUnion id
      change U.card ≤ B.card + M.card at hbound
      have hMU : M.biUnion id ⊆ U := by
        intro x hx
        obtain ⟨e, heM, hxe⟩ := Finset.mem_biUnion.mp hx
        exact Finset.mem_biUnion.mpr ⟨e, hMB heM, hxe⟩
      by_cases hgood : b.card = 2 ∧ Disjoint b (M.biUnion id)
      · have hbM : b ∉ M := by
          intro h
          exact hb (hMB h)
        refine ⟨insert b M, ?_, ?_, ?_, ?_⟩
        · intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hMB he)
        · rw [Finset.coe_insert]
          refine hMdis.insert ?_
          intro e he _
          have hde : Disjoint b e := by
            apply Finset.disjoint_left.mpr
            intro x hxb hxe
            exact (Finset.disjoint_left.mp hgood.2) hxb
              (Finset.mem_biUnion.mpr ⟨e, he, hxe⟩)
          exact ⟨hde, hde.symm⟩
        · intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact hgood.1
          · exact hMtwo e he
        · rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hb,
              Finset.card_insert_of_notMem hbM]
          have hu := Finset.card_union_le b U
          change (b ∪ U).card ≤ _
          omega
      · have hdiff : (b \ U).card ≤ 1 := by
          by_cases hsmall : b.card ≤ 1
          · exact (Finset.card_le_card (Finset.sdiff_subset)).trans hsmall
          · have hb2 : b.card = 2 := by omega
            have hnotdis : ¬Disjoint b (M.biUnion id) := by
              intro hd
              exact hgood ⟨hb2, hd⟩
            obtain ⟨x, hxb, hxM⟩ := Finset.not_disjoint_iff.mp hnotdis
            have hinter : 1 ≤ (b ∩ U).card := Finset.one_le_card.mpr
              ⟨x, Finset.mem_inter.mpr ⟨hxb, hMU hxM⟩⟩
            have hsum := Finset.card_sdiff_add_card_inter b U
            omega
        refine ⟨M, ?_, hMdis, hMtwo, ?_⟩
        · intro e he
          exact Finset.mem_insert_of_mem (hMB he)
        · rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hb]
          have hu := Finset.card_sdiff_add_card b U
          change (b ∪ U).card ≤ _
          omega
