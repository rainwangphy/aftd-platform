import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteThreeSetStableMaximumPackingsCoverSupport

/-!
# finite_three_set_stable_nonextendable_triple_patterns

Topic: graphs   Node: 20250ff892a6

Provenance: helper lemma. Elementary packing exchange in the triangle packing-cover campaign, related to arXiv:2610.15539, Section 1.

In a finite family of three-element sets where every point can be omitted by some maximum packing, if a triple belongs to no maximum packing, then for each of its points there is a maximum packing omitting that point and covering both of the other two.
-/

theorem finite_three_set_stable_nonextendable_triple_patterns
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (k : ℕ)
    (hthree : ∀ t ∈ F, t.card = 3)
    (hmax : ∀ P : Finset (Finset α), P ⊆ F →
      (P : Set (Finset α)).Pairwise Disjoint → P.card ≤ k)
    (hstable : ∀ x ∈ F.biUnion id, ∃ P : Finset (Finset α),
      P ⊆ F ∧ (P : Set (Finset α)).Pairwise Disjoint ∧ P.card = k ∧
      ∀ s ∈ P, x ∉ s)
    (T : Finset α) (hTF : T ∈ F)
    (hnonextendable : ∀ P : Finset (Finset α), P ⊆ F →
      (P : Set (Finset α)).Pairwise Disjoint → P.card = k → T ∉ P) :
    ∀ x ∈ T, ∃ P : Finset (Finset α),
      P ⊆ F ∧ (P : Set (Finset α)).Pairwise Disjoint ∧ P.card = k ∧
      (∀ s ∈ P, x ∉ s) ∧
      (∀ y ∈ T, y ≠ x → ∃ s ∈ P, y ∈ s) := by
  open Finset in
  intro x hxT
  have hTcard : T.card = 3 := hthree T hTF
  have hx_biUnion : x ∈ F.biUnion id := mem_biUnion.2 ⟨T, hTF, hxT⟩
  obtain ⟨P, hPF, hPdisj, hPcard, hPnotx⟩ := hstable x hx_biUnion
  refine ⟨P, hPF, hPdisj, hPcard, hPnotx, ?_⟩
  by_contra! hmiss
  obtain ⟨y, hyT, hyne, hPnoty⟩ := hmiss
  let C := P.filter (fun s => ¬ Disjoint s T)
  have hC_le_one : C.card ≤ 1 := by
    rw [card_le_one_iff]
    intro a b ha hb
    rw [mem_filter] at ha hb
    obtain ⟨haP, hadisj⟩ := ha
    obtain ⟨hbP, hbdisj⟩ := hb
    rw [disjoint_iff_inter_eq_empty] at hadisj hbdisj
    have ha_nonempty : (a ∩ T).Nonempty := nonempty_iff_ne_empty.mpr hadisj
    have hb_nonempty : (b ∩ T).Nonempty := nonempty_iff_ne_empty.mpr hbdisj
    obtain ⟨za, hza⟩ := ha_nonempty
    obtain ⟨zb, hzb⟩ := hb_nonempty
    rw [mem_inter] at hza hzb
    have hza_diff : za ∈ T \ {x, y} := by
      rw [mem_sdiff, mem_insert, mem_singleton, not_or]
      refine ⟨hza.2, ?_⟩
      constructor
      · rintro rfl; exact hPnotx a haP hza.1
      · rintro rfl; exact hPnoty a haP hza.1
    have hzb_diff : zb ∈ T \ {x, y} := by
      rw [mem_sdiff, mem_insert, mem_singleton, not_or]
      refine ⟨hzb.2, ?_⟩
      constructor
      · rintro rfl; exact hPnotx b hbP hzb.1
      · rintro rfl; exact hPnoty b hbP hzb.1
    have hsub : ({x, y} : Finset α) ⊆ T := by
      rw [insert_subset_iff, singleton_subset_iff]
      exact ⟨hxT, hyT⟩
    have hcard_diff : (T \ {x, y}).card = 1 := by
      rw [card_sdiff_of_subset hsub]
      have hxy_card : ({x, y} : Finset α).card = 2 := card_pair hyne.symm
      rw [hxy_card, hTcard]
    obtain ⟨z, hz⟩ := card_eq_one.mp hcard_diff
    have hza_z : za = z := by
      have := hza_diff
      rw [hz, mem_singleton] at this
      exact this
    have hzb_z : zb = z := by
      have := hzb_diff
      rw [hz, mem_singleton] at this
      exact this
    have h_eq : za = zb := hza_z.trans hzb_z.symm
    by_contra hab
    have hdisj : Disjoint a b := hPdisj haP hbP hab
    have h_inter : za ∈ a ∩ b := mem_inter.mpr ⟨hza.1, h_eq ▸ hzb.1⟩
    rw [disjoint_iff_inter_eq_empty] at hdisj
    rw [hdisj] at h_inter
    exact notMem_empty za h_inter
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hC_le_one with hC0 | hC1
  · have hCempty : C = ∅ := card_eq_zero.mp hC0
    have hTnotP : T ∉ P := by
      intro hTP
      have hCmem : T ∈ C := by
        rw [mem_filter]
        refine ⟨hTP, ?_⟩
        rw [disjoint_iff_inter_eq_empty, inter_self]
        intro hTempty
        rw [hTempty] at hTcard
        contradiction
      rw [hCempty] at hCmem
      exact notMem_empty T hCmem
    have hP'disj : ((insert T P : Finset (Finset α)) : Set (Finset α)).Pairwise Disjoint := by
      rw [coe_insert, Set.pairwise_insert_of_symm]
      refine ⟨hPdisj, ?_⟩
      intro b hb _
      have hbP : b ∈ P := hb
      have hbnotC : b ∉ C := by rw [hCempty]; exact notMem_empty b
      rw [mem_filter, not_and] at hbnotC
      have := hbnotC hbP
      have hdisj : Disjoint b T := not_not.mp this
      exact hdisj.symm
    have hP'sub : insert T P ⊆ F := insert_subset hTF hPF
    have hP'card : (insert T P).card = k + 1 := by
      rw [card_insert_of_notMem hTnotP, hPcard]
    have hle := hmax (insert T P) hP'sub hP'disj
    rw [hP'card] at hle
    exact Nat.not_succ_le_self k hle
  · obtain ⟨s0, hs0⟩ := card_eq_one.mp hC1
    have hs0C : s0 ∈ C := by rw [hs0, mem_singleton]
    rw [mem_filter] at hs0C
    have hs0P : s0 ∈ P := hs0C.1
    have hTnot : T ∉ P \ {s0} := by
      intro hTin
      rw [mem_sdiff, mem_singleton] at hTin
      have hTC : T ∈ C := by
        rw [mem_filter]
        refine ⟨hTin.1, ?_⟩
        rw [disjoint_iff_inter_eq_empty, inter_self]
        intro hTempty
        rw [hTempty] at hTcard
        contradiction
      rw [hs0, mem_singleton] at hTC
      exact hTin.2 hTC
    have hP'disj : ((insert T (P \ {s0}) : Finset (Finset α)) : Set (Finset α)).Pairwise Disjoint := by
      rw [coe_insert, Set.pairwise_insert_of_symm]
      refine ⟨hPdisj.mono (by rw [coe_sdiff, coe_singleton]; exact Set.sdiff_subset), ?_⟩
      intro b hb _
      rw [mem_coe, mem_sdiff, mem_singleton] at hb
      have hbP : b ∈ P := hb.1
      have hbne : b ≠ s0 := hb.2
      have hbnotC : b ∉ C := by rw [hs0, mem_singleton]; exact hbne
      rw [mem_filter, not_and] at hbnotC
      have := hbnotC hbP
      have hdisj : Disjoint b T := not_not.mp this
      exact hdisj.symm
    have hP'card : (insert T (P \ {s0})).card = k := by
      rw [card_insert_of_notMem hTnot]
      rw [card_sdiff_of_subset (singleton_subset_iff.mpr hs0P), card_singleton]
      rw [hPcard]
      have hk : 1 ≤ k := by
        have : 1 ≤ P.card := card_pos.mpr ⟨s0, hs0P⟩
        rwa [hPcard] at this
      exact Nat.sub_add_cancel hk
    have hP'sub : insert T (P \ {s0}) ⊆ F :=
      insert_subset hTF (sdiff_subset.trans hPF)
    have hTinP' : T ∈ insert T (P \ {s0}) := mem_insert_self T _
    exact hnonextendable (insert T (P \ {s0})) hP'sub hP'disj hP'card hTinP'
