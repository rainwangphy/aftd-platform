import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteThreeSetStableMaximumPackingsCoverSupport

/-!
# finite_three_set_stable_small_cover_supported_by_two_maximum_packings

Topic: graphs   Node: c1f851b05d85

Provenance: helper lemma. Elementary consequence of the maximum-packing exchange lemma in the triangle packing-cover campaign.

For a stable finite three-set family with packing number k, any cover of size at most k+1 using only active points is contained in the union of the point sets of any chosen maximum packing and some second maximum packing.
-/

theorem finite_three_set_stable_small_cover_supported_by_two_maximum_packings
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (k : ℕ)
    (hthree : ∀ t ∈ F, t.card = 3)
    (hmax : ∀ P : Finset (Finset α), P ⊆ F →
      (P : Set (Finset α)).Pairwise Disjoint → P.card ≤ k)
    (hstable : ∀ x ∈ F.biUnion id, ∃ P : Finset (Finset α),
      P ⊆ F ∧ (P : Set (Finset α)).Pairwise Disjoint ∧ P.card = k ∧
      ∀ s ∈ P, x ∉ s)
    (P : Finset (Finset α)) (hPF : P ⊆ F)
    (hPdis : (P : Set (Finset α)).Pairwise Disjoint) (hPk : P.card = k)
    (C : Finset α) (hactive : C ⊆ F.biUnion id)
    (hcover : ∀ t ∈ F, ¬ Disjoint C t) (hcard : C.card ≤ k + 1) :
    ∃ Q : Finset (Finset α), Q ⊆ F ∧
      (Q : Set (Finset α)).Pairwise Disjoint ∧ Q.card = k ∧
      C ⊆ P.biUnion id ∪ Q.biUnion id := by
  classical
  set U : Finset α := P.biUnion id with hU
  have hex : ∀ t ∈ P, ∃ c, c ∈ C ∧ c ∈ t := fun t ht =>
    Finset.not_disjoint_iff.mp (hcover t (hPF ht))
  choose f hfC hft using hex
  let g : {t // t ∈ P} → α := fun s => f s.1 s.2
  have hinj : Function.Injective g := by
    rintro ⟨t, ht⟩ ⟨t', ht'⟩ heq
    simp only [g] at heq
    by_contra hne
    have htne : t ≠ t' := fun h => hne (Subtype.ext h)
    have hdis := hPdis ht ht' htne
    rw [Finset.disjoint_left] at hdis
    exact (hdis (hft t ht)) (by rw [heq]; exact hft t' ht')
  have hIcard : (P.attach.image g).card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, hPk]
  have hIC : P.attach.image g ⊆ C := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨s, hs, rfl⟩ := ha
    exact hfC s.1 s.2
  have hIU : P.attach.image g ⊆ U := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨s, hs, rfl⟩ := ha
    rw [hU, Finset.mem_biUnion]
    exact ⟨s.1, s.2, hft s.1 s.2⟩
  have hDcard : k ≤ (C ∩ U).card := by
    have := Finset.card_le_card (Finset.subset_inter hIC hIU)
    rwa [hIcard] at this
  have hle1 : (C \ U).card ≤ 1 := by
    have hsplit := Finset.card_inter_add_card_sdiff C U
    omega
  by_cases hempty : C \ U = ∅
  · refine ⟨P, hPF, hPdis, hPk, ?_⟩
    have hCU : C ⊆ U := Finset.sdiff_eq_empty_iff_subset.mp hempty
    intro a ha
    exact Finset.mem_union.mpr (Or.inl (hU ▸ hCU ha))
  · have hne : (C \ U).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard1 : (C \ U).card = 1 := by
      have hpos : 0 < (C \ U).card := Finset.card_pos.mpr hne
      omega
    obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp hcard1
    have hxmem : x ∈ C \ U := by rw [hx_eq]; exact Finset.mem_singleton.mpr rfl
    have hxC : x ∈ C := (Finset.mem_sdiff.mp hxmem).1
    have hxactive : x ∈ F.biUnion id := hactive hxC
    obtain ⟨Q, hQF, hQdis, hQk, s, hsQ, hxs⟩ :=
      finite_three_set_stable_maximum_packings_cover_support F k hthree hmax hstable x hxactive
    refine ⟨Q, hQF, hQdis, hQk, ?_⟩
    intro a ha
    by_cases haU : a ∈ U
    · exact Finset.mem_union.mpr (Or.inl (hU ▸ haU))
    · have hain : a ∈ C \ U := Finset.mem_sdiff.mpr ⟨ha, haU⟩
      rw [hx_eq] at hain
      have hax : a = x := Finset.mem_singleton.mp hain
      rw [hax]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨s, hsQ, hxs⟩))
