import AFTD.Prelude

/-!
# finite_linear_packing_support_quadratic_kernel

Topic: graphs   Node: f9fd1f2e79b5

Provenance: helper lemma. Finite support-signature compression in the triangle packing-cover campaign.

In a finite linear three-set family covered by a packing P, if each packed triple has at most one singly forced point, there is a set V of at most 5k + 9k(k-1)/2 points, k=|P|, containing P support and retaining a family member with each possible nonempty support intersection.
-/

private lemma finite_linear_packing_support_quadratic_kernel_disjoint_powersetCard
    {α : Type*} [DecidableEq α] (a b : Finset α) (h : a ∩ b = ∅) :
    Disjoint (a.powersetCard 2) (b.powersetCard 2) := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext s
  rw [Finset.mem_inter, Finset.mem_powersetCard, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨h1, h2c⟩, h3', _⟩
    exfalso
    have hsub2 : s ⊆ a ∩ b := fun x hx => Finset.mem_inter.mpr ⟨h1 hx, h3' hx⟩
    rw [h] at hsub2
    have hs0 : s = ∅ := Finset.subset_empty.mp hsub2
    rw [hs0] at h2c
    simp at h2c
  · intro hh; simp at hh

private lemma finite_linear_packing_support_quadratic_kernel_choose_identity (n : ℕ) :
    (3*n).choose 2 = 9 * n.choose 2 + 3*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have step : ∀ m : ℕ, (m+1).choose 2 = m.choose 2 + m := by
      intro m
      have := Nat.choose_succ_succ m 1
      simp only [Nat.choose_one_right] at this
      rw [this]; ring
    have h3 : 3 * (n+1) = 3*n + 3 := by ring
    rw [h3]
    rw [show (3*n + 3) = (3*n+2)+1 from rfl, step]
    rw [show (3*n+2) = (3*n+1)+1 from rfl, step]
    rw [show (3*n+1) = (3*n)+1 from rfl, step]
    rw [ih, Nat.choose_succ_succ, Nat.choose_one_right]
    ring

private lemma finite_linear_packing_support_quadratic_kernel_eq_singleton
    {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (hcard : s.card = 1) (ha : a ∈ s) : s = {a} := by
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard
  rw [hb, Finset.mem_singleton] at ha
  rw [hb, ← ha]

set_option maxHeartbeats 1000000 in
private lemma finite_linear_packing_support_quadratic_kernel_two_support_card
    {α : Type*} [DecidableEq α] (F P : Finset (Finset α))
    (hsub : P ⊆ F)
    (hthree : ∀ t ∈ F, t.card = 3)
    (hlinear : (F : Set (Finset α)).Pairwise (fun a b => (a ∩ b).card ≤ 1))
    (hpack : (P : Set (Finset α)).Pairwise Disjoint) :
    (F.filter (fun t => (t ∩ P.biUnion id).card = 2)).card ≤ 9 * P.card.choose 2 := by
  set U := P.biUnion id with hUdef
  set n := P.card with hndef
  have hP3 : ∀ p ∈ P, p.card = 3 := fun p hp => hthree p (hsub hp)
  have hUcard : U.card = 3 * n := by
    rw [hUdef]
    change (P.biUnion (fun p => p)).card = 3 * P.card
    rw [Finset.card_biUnion (t := fun p => p) (by
      intro a ha b hb hab
      exact hpack ha hb hab)]
    have hcongr : (∑ u ∈ P, ((fun p => p) u).card) = (∑ u ∈ P, 3) := by
      apply Finset.sum_congr rfl; intro p hp; exact hP3 p hp
    rw [hcongr, Finset.sum_const_nat (fun p hp => rfl)]; ring
  set sameBlockPairs := P.biUnion (fun p : Finset α => p.powersetCard 2) with hsBP
  have hsBP_sub : sameBlockPairs ⊆ U.powersetCard 2 := by
    intro s hs
    rw [hsBP, Finset.mem_biUnion] at hs
    obtain ⟨p, hp, hsp⟩ := hs
    rw [Finset.mem_powersetCard] at hsp ⊢
    exact ⟨hsp.1.trans (Finset.subset_biUnion_of_mem (fun p => p) hp), hsp.2⟩
  have hsBP_card : sameBlockPairs.card = 3 * n := by
    rw [hsBP]
    rw [Finset.card_biUnion (t := (fun p : Finset α => p.powersetCard 2)) (by
      intro a ha b hb hab
      simp only [Function.onFun]
      exact finite_linear_packing_support_quadratic_kernel_disjoint_powersetCard a b (by
        rw [← Finset.disjoint_iff_inter_eq_empty]; exact hpack ha hb hab))]
    have hcongr : (∑ u ∈ P, (u.powersetCard 2).card) = (∑ u ∈ P, 3) := by
      apply Finset.sum_congr rfl; intro p hp
      rw [Finset.card_powersetCard, hP3 p hp]; norm_num
    rw [hcongr, Finset.sum_const_nat (fun p hp => rfl)]; ring
  have hinj : Set.InjOn (fun t => t ∩ U) ↑(F.filter (fun t => (t ∩ U).card = 2)) := by
    intro t1 ht1 t2 ht2 heq
    simp only at heq
    rw [Finset.mem_coe, Finset.mem_filter] at ht1 ht2
    by_contra hne
    have hle := hlinear ht1.1 ht2.1 hne
    have hsub' : (t1 ∩ U) ⊆ t1 ∩ t2 := by
      intro x hx
      obtain ⟨hx1, hxU⟩ := Finset.mem_inter.mp hx
      have hx2 : x ∈ t2 := by
        have hxU' : x ∈ t2 ∩ U := by
          rw [← heq]; exact Finset.mem_inter.mpr ⟨hx1, hxU⟩
        exact (Finset.mem_inter.mp hxU').1
      exact Finset.mem_inter.mpr ⟨hx1, hx2⟩
    have hge : 2 ≤ (t1 ∩ t2).card := by
      rw [← ht1.2]; exact Finset.card_le_card hsub'
    omega
  have hAcard : ((F.filter (fun t => (t ∩ U).card = 2)).image (fun t => t ∩ U)).card
      = (F.filter (fun t => (t ∩ U).card = 2)).card := by
    rw [Finset.card_image_iff.mpr hinj]
  have hA_legal : (F.filter (fun t => (t ∩ U).card = 2)).image (fun t => t ∩ U)
      ⊆ U.powersetCard 2 \ sameBlockPairs := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨t, htS2, rfl⟩ := hs
    obtain ⟨htF, htc⟩ := Finset.mem_filter.mp htS2
    rw [Finset.mem_sdiff, Finset.mem_powersetCard]
    refine ⟨⟨Finset.inter_subset_right, htc⟩, ?_⟩
    intro hmem
    rw [hsBP, Finset.mem_biUnion] at hmem
    obtain ⟨p, hp, hpmem⟩ := hmem
    rw [Finset.mem_powersetCard] at hpmem
    obtain ⟨hsubp, _⟩ := hpmem
    have hsub_tp : (t ∩ U) ⊆ t ∩ p := fun x hx =>
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hsubp hx⟩
    have hge : 2 ≤ (t ∩ p).card := by rw [← htc]; exact Finset.card_le_card hsub_tp
    have hne : t ≠ p := by
      intro heq
      rw [heq] at htc
      have hpU : p ∩ U = p := Finset.inter_eq_left.mpr (Finset.subset_biUnion_of_mem (fun p => p) hp)
      rw [hpU, hP3 p hp] at htc
      omega
    have := hlinear htF (hsub hp) hne
    omega
  have hlegalcard : (U.powersetCard 2 \ sameBlockPairs).card = 9 * n.choose 2 := by
    rw [Finset.card_sdiff]
    rw [show sameBlockPairs ∩ U.powersetCard 2 = sameBlockPairs from
      Finset.inter_eq_left.mpr hsBP_sub]
    rw [Finset.card_powersetCard, hUcard, hsBP_card]
    have hid := finite_linear_packing_support_quadratic_kernel_choose_identity n
    omega
  have hfin : (F.filter (fun t => (t ∩ U).card = 2)).card ≤ 9 * n.choose 2 := by
    calc (F.filter (fun t => (t ∩ U).card = 2)).card
        = ((F.filter (fun t => (t ∩ U).card = 2)).image (fun t => t ∩ U)).card := hAcard.symm
      _ ≤ (U.powersetCard 2 \ sameBlockPairs).card := Finset.card_le_card hA_legal
      _ = 9 * n.choose 2 := hlegalcard
  rwa [hndef] at hfin

set_option maxHeartbeats 1000000 in
private lemma finite_linear_packing_support_quadratic_kernel_supp_card
    {α : Type*} [DecidableEq α] (F P : Finset (Finset α))
    (hsub : P ⊆ F)
    (hthree : ∀ t ∈ F, t.card = 3)
    (hpack : (P : Set (Finset α)).Pairwise Disjoint)
    (hforced : ∀ p ∈ P,
      (((F.filter (fun t => (t ∩ P.biUnion id).card = 1)).biUnion id) ∩ p).card ≤ 1) :
    (((F.filter (fun t => (t ∩ P.biUnion id).card = 1)).biUnion id) ∩ (P.biUnion id)).card
      ≤ P.card := by
  set U := P.biUnion id with hUdef
  set n := P.card with hndef
  set T1 := F.filter (fun t => (t ∩ U).card = 1) with hT1def
  set suppSet := (T1.biUnion id) ∩ U with hsuppdef
  have hP3 : ∀ p ∈ P, p.card = 3 := fun p hp => hthree p (hsub hp)
  have hsupp_biUnion : suppSet = P.biUnion (fun p => suppSet ∩ p) := by
    ext x
    rw [Finset.mem_biUnion]
    constructor
    · intro hx
      rw [hsuppdef, Finset.mem_inter] at hx
      obtain ⟨hxT, hxU⟩ := hx
      rw [hUdef, Finset.mem_biUnion] at hxU
      obtain ⟨p, hp, hxp⟩ := hxU
      refine ⟨p, hp, ?_⟩
      exact Finset.mem_inter.mpr ⟨by
        rw [hsuppdef]
        exact Finset.mem_inter.mpr ⟨hxT, Finset.mem_biUnion.mpr ⟨p, hp, hxp⟩⟩, hxp⟩
    · rintro ⟨p, hp, hxp⟩
      exact (Finset.mem_inter.mp hxp).1
  have hcard : suppSet.card ≤ n := by
    rw [hsupp_biUnion]
    rw [Finset.card_biUnion (t := (fun p => suppSet ∩ p)) (by
      intro a ha b hb hab
      simp only [Function.onFun]
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext x
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨_, hxa⟩, ⟨_, hxb⟩⟩
        have hp_inter : a ∩ b = ∅ := by
          rw [← Finset.disjoint_iff_inter_eq_empty]; exact hpack ha hb hab
        have : x ∈ a ∩ b := Finset.mem_inter.mpr ⟨hxa, hxb⟩
        rw [hp_inter] at this
        exact this
      · intro h; exact absurd h (by simp))]
    have hle : ∀ p ∈ P, (suppSet ∩ p).card ≤ 1 := by
      intro p hp
      have hsub1 : suppSet ∩ p ⊆ (T1.biUnion id) ∩ p := by
        intro x hx
        rw [Finset.mem_inter] at hx ⊢
        exact ⟨(Finset.mem_inter.mp hx.1).1, hx.2⟩
      exact le_trans (Finset.card_le_card hsub1) (by rw [hT1def]; exact hforced p hp)
    calc (∑ p ∈ P, (suppSet ∩ p).card) ≤ ∑ p ∈ P, 1 := by
          apply Finset.sum_le_sum; intro p hp; exact hle p hp
      _ = n := by rw [Finset.sum_const_nat (fun p hp => rfl)]; ring
  rw [hndef]
  exact hcard

theorem finite_linear_packing_support_quadratic_kernel
    {α : Type*} [DecidableEq α] (F P : Finset (Finset α))
    (hsub : P ⊆ F)
    (hthree : ∀ t ∈ F, t.card = 3)
    (hlinear : (F : Set (Finset α)).Pairwise (fun a b => (a ∩ b).card ≤ 1))
    (hpack : (P : Set (Finset α)).Pairwise Disjoint)
    (hcover : ∀ t ∈ F, ¬ Disjoint (P.biUnion id) t)
    (hforced : ∀ p ∈ P,
      (((F.filter (fun t => (t ∩ P.biUnion id).card = 1)).biUnion id) ∩ p).card ≤ 1) :
    ∃ V : Finset α, P.biUnion id ⊆ V ∧
      V.card ≤ 5 * P.card + 9 * (P.card * (P.card - 1) / 2) ∧
      ∀ t ∈ F, ∃ s ∈ F, s ⊆ V ∧ s ∩ P.biUnion id = t ∩ P.biUnion id := by
  classical
  set U := P.biUnion id with hUdef
  set n := P.card with hndef
  set T1 := F.filter (fun t => (t ∩ U).card = 1) with hT1def
  set S2 := F.filter (fun t => (t ∩ U).card = 2) with hS2def
  set suppSet := (T1.biUnion id) ∩ U with hsuppdef
  set wfun : α → Finset α :=
    (fun a => if h : (∃ t ∈ T1, a ∈ t) then Classical.choose h else ∅) with hwfun
  set W := suppSet.image wfun with hWdef
  set X := S2.biUnion id with hXdef
  set Y := W.biUnion id with hYdef
  set V := U ∪ (X ∪ Y) with hVdef
  have hUcard : U.card = 3 * n := by
    rw [hUdef]; change (P.biUnion (fun p => p)).card = 3 * P.card
    rw [Finset.card_biUnion (t := fun p => p) (by
      intro a ha b hb hab; exact hpack ha hb hab)]
    have hcongr : (∑ u ∈ P, ((fun p => p) u).card) = (∑ u ∈ P, 3) := by
      apply Finset.sum_congr rfl; intro p hp; exact hthree p (hsub hp)
    rw [hcongr, Finset.sum_const_nat (fun p hp => rfl)]; ring
  have hS2card : S2.card ≤ 9 * n.choose 2 := by
    rw [hndef, hS2def]
    exact finite_linear_packing_support_quadratic_kernel_two_support_card F P hsub hthree hlinear hpack
  have hsupp_card : suppSet.card ≤ n := by
    rw [hsuppdef, hT1def, hUdef, hndef]
    exact finite_linear_packing_support_quadratic_kernel_supp_card F P hsub hthree hpack hforced
  have hwfun_mem : ∀ a ∈ suppSet, wfun a ∈ T1 ∧ a ∈ wfun a := by
    intro a ha
    have ha' : a ∈ T1.biUnion id ∩ U := hsuppdef ▸ ha
    have hmemU : a ∈ T1.biUnion id := (Finset.mem_inter.mp ha').1
    rw [Finset.mem_biUnion] at hmemU
    obtain ⟨t, ht, hat⟩ := hmemU
    have hex : ∃ t ∈ T1, a ∈ t := ⟨t, ht, hat⟩
    have hwfun_eq : wfun a = Classical.choose hex := by
      rw [hwfun]; exact dif_pos hex
    rw [hwfun_eq]
    exact Classical.choose_spec hex
  have hW_sub : W ⊆ F := by
    intro w hw
    rw [hWdef, Finset.mem_image] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    have hT1a : wfun a ∈ T1 := (hwfun_mem a ha).1
    have : wfun a ∈ F.filter (fun t => (t ∩ U).card = 1) := by rw [← hT1def]; exact hT1a
    exact (Finset.mem_filter.mp this).1
  have hWcard : W.card ≤ n := by
    calc W.card ≤ suppSet.card := by rw [hWdef]; exact Finset.card_image_le
      _ ≤ n := hsupp_card
  have hwfun_sdiff : ∀ a ∈ suppSet, (wfun a \ U).card ≤ 2 := by
    intro a ha
    have hT1a : wfun a ∈ T1 := (hwfun_mem a ha).1
    have hc1 : (wfun a ∩ U).card = 1 := by
      have hh : wfun a ∈ F.filter (fun t => (t ∩ U).card = 1) := by rw [← hT1def]; exact hT1a
      exact (Finset.mem_filter.mp hh).2
    have hF : wfun a ∈ F := hW_sub (by rw [hWdef]; exact Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    have hc3 : (wfun a).card = 3 := hthree _ hF
    rw [Finset.card_sdiff]
    have hUi : (U ∩ wfun a).card = 1 := by rw [Finset.inter_comm]; exact hc1
    rw [hUi, hc3]
  have hXU : (X \ U).card ≤ S2.card := by
    rw [hXdef]
    have heq : (S2.biUnion id) \ U = S2.biUnion (fun t => t \ U) := by
      ext x; constructor
      · intro hx
        rw [Finset.mem_sdiff] at hx; obtain ⟨hxB, hxU⟩ := hx
        rw [Finset.mem_biUnion] at hxB ⊢; obtain ⟨t, ht, hxt⟩ := hxB
        exact ⟨t, ht, Finset.mem_sdiff.mpr ⟨hxt, hxU⟩⟩
      · intro hx
        rw [Finset.mem_biUnion] at hx; obtain ⟨t, ht, hxt⟩ := hx
        rw [Finset.mem_sdiff] at hxt ⊢
        exact ⟨Finset.mem_biUnion.mpr ⟨t, ht, hxt.1⟩, hxt.2⟩
    rw [heq]
    calc (S2.biUnion (fun t => t \ U)).card ≤ ∑ t ∈ S2, (t \ U).card := Finset.card_biUnion_le
      _ = ∑ t ∈ S2, 1 := by
          apply Finset.sum_congr rfl; intro t ht
          rw [hS2def, Finset.mem_filter] at ht
          rw [Finset.card_sdiff]
          have hUi : (U ∩ t).card = 2 := by rw [Finset.inter_comm]; exact ht.2
          rw [hUi, hthree t ht.1]
      _ = S2.card := by rw [Finset.sum_const_nat (fun t ht => rfl)]; ring
  have hYU : (Y \ U).card ≤ 2 * n := by
    rw [hYdef]
    have heq : (W.biUnion id) \ U = W.biUnion (fun w => w \ U) := by
      ext x; constructor
      · intro hx
        rw [Finset.mem_sdiff] at hx; obtain ⟨hxB, hxU⟩ := hx
        rw [Finset.mem_biUnion] at hxB ⊢; obtain ⟨t, ht, hxt⟩ := hxB
        exact ⟨t, ht, Finset.mem_sdiff.mpr ⟨hxt, hxU⟩⟩
      · intro hx
        rw [Finset.mem_biUnion] at hx; obtain ⟨t, ht, hxt⟩ := hx
        rw [Finset.mem_sdiff] at hxt ⊢
        exact ⟨Finset.mem_biUnion.mpr ⟨t, ht, hxt.1⟩, hxt.2⟩
    rw [heq]
    calc (W.biUnion (fun w => w \ U)).card ≤ ∑ w ∈ W, (w \ U).card := Finset.card_biUnion_le
      _ ≤ ∑ w ∈ W, 2 := by
          apply Finset.sum_le_sum; intro w hw
          rw [hWdef, Finset.mem_image] at hw
          obtain ⟨a, ha, rfl⟩ := hw
          exact hwfun_sdiff a ha
      _ = W.card * 2 := by rw [Finset.sum_const_nat (fun w hw => rfl)]
      _ ≤ n * 2 := by apply Nat.mul_le_mul_right; exact hWcard
      _ = 2 * n := by ring
  have hVpart : ((X ∪ Y) \ U).card ≤ (X \ U).card + (Y \ U).card := by
    have heq : (X ∪ Y) \ U = (X \ U) ∪ (Y \ U) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    rw [heq]; exact Finset.card_union_le _ _
  have hV_eq : V = U ∪ ((X ∪ Y) \ U) := by
    rw [hVdef]
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  have hVcard : V.card ≤ 5 * n + 9 * n.choose 2 := by
    rw [hV_eq]
    have h1 : (U ∪ ((X ∪ Y) \ U)).card ≤ U.card + ((X ∪ Y) \ U).card := Finset.card_union_le _ _
    omega
  have hUV : U ⊆ V := by rw [hVdef]; exact Finset.subset_union_left
  have hXV : X ⊆ V := by
    rw [hVdef]; exact Finset.subset_union_left.trans Finset.subset_union_right
  have hYV : Y ⊆ V := by
    rw [hVdef]; exact Finset.subset_union_right.trans Finset.subset_union_right
  refine ⟨V, ?_, ?_, ?_⟩
  · exact hUV
  · have hv := hVcard
    rw [hndef] at hv
    rw [Nat.choose_two_right] at hv
    exact hv
  · intro t ht
    have hcd := hcover t ht
    have hne0 : U ∩ t ≠ ∅ := by
      intro h
      exact hcd (Finset.disjoint_iff_inter_eq_empty.mpr h)
    have hne : t ∩ U ≠ ∅ := by rw [Finset.inter_comm]; exact hne0
    have hpos : 0 < (t ∩ U).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    have htcard : t.card = 3 := hthree t ht
    have hle3 : (t ∩ U).card ≤ 3 := by
      rw [← htcard]; exact Finset.card_le_card Finset.inter_subset_left
    have hc : (t ∩ U).card = 1 ∨ (t ∩ U).card = 2 ∨ (t ∩ U).card = 3 := by omega
    rcases hc with h1 | h2 | h3
    · obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp h1
      have ha_inter : a ∈ t ∩ U := by rw [ha_eq]; exact Finset.mem_singleton_self a
      have hat : a ∈ t := (Finset.mem_inter.mp ha_inter).1
      have hau : a ∈ U := (Finset.mem_inter.mp ha_inter).2
      have ha_supp : a ∈ suppSet := by
        rw [hsuppdef, Finset.mem_inter]
        refine ⟨?_, hau⟩
        rw [Finset.mem_biUnion]
        refine ⟨t, ?_, hat⟩
        rw [hT1def, Finset.mem_filter]
        exact ⟨ht, h1⟩
      have hw := hwfun_mem a ha_supp
      have hwa_W : wfun a ∈ W := by rw [hWdef]; exact Finset.mem_image.mpr ⟨a, ha_supp, rfl⟩
      refine ⟨wfun a, hW_sub hwa_W, ?_, ?_⟩
      · have hsubY : wfun a ⊆ Y := by
          rw [hYdef]; exact Finset.subset_biUnion_of_mem (fun w => w) hwa_W
        exact fun x hx => hYV (hsubY hx)
      · have hwsupp : wfun a ∩ U = {a} := by
          apply finite_linear_packing_support_quadratic_kernel_eq_singleton
          · have hT1a : wfun a ∈ T1 := hw.1
            have hmem : wfun a ∈ F.filter (fun s => (s ∩ U).card = 1) := by
              rw [← hT1def]; exact hT1a
            exact (Finset.mem_filter.mp hmem).2
          · exact Finset.mem_inter.mpr ⟨hw.2, hau⟩
        rw [hwsupp, ← ha_eq]
    · have htS2 : t ∈ S2 := by rw [hS2def, Finset.mem_filter]; exact ⟨ht, h2⟩
      have htX : t ⊆ X := by
        rw [hXdef]; exact Finset.subset_biUnion_of_mem (fun u => u) htS2
      refine ⟨t, ht, ?_, rfl⟩
      exact fun x hx => hXV (htX hx)
    · have htU : t ⊆ U := by
        rw [← Finset.inter_eq_left]
        exact Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h3, htcard])
      refine ⟨t, ht, ?_, rfl⟩
      exact fun x hx => hUV (htU hx)
