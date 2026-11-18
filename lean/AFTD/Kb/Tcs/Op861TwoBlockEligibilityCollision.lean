import AFTD.Prelude
import AFTD.Kb.Tcs.Op861PartitionProfileObstruction

/-!
# op861_two_block_eligibility_collision

Topic: graphs   Node: ea8aa9a3274c

Provenance: helper lemma. Two-block eligibility obstruction investigated in Codex session on OP-861.

For any two nonempty palette blocks of different sizes summing to 2k−1, suppose each side specifies eligible colors using only the number of colors from the smaller block and that every k-set meets its eligible set. Then some two k-sets have intersection exactly one and share a color that is eligible on both sides. Thus this color-eligibility construction cannot safely color even at threshold one.
-/

open Finset

lemma op861_two_block_eligibility_collision_finset_partition_two {α : Type*} [DecidableEq α]
    (s : Finset α) (a b : ℕ) (h : s.card = a + b) :
    ∃ u v : Finset α, Disjoint u v ∧ u ∪ v = s ∧ u.card = a ∧ v.card = b := by
  obtain ⟨u, hu, hua⟩ : ∃ u ⊆ s, u.card = a := exists_subset_card_eq (by omega)
  refine ⟨u, s \ u, disjoint_sdiff_self_right, union_sdiff_of_subset hu, hua, ?_⟩
  rw [card_sdiff_of_subset hu, h, hua]
  omega

lemma op861_two_block_eligibility_collision_ha_step (k : ℕ) (P : Finset (Fin (2*k - 1)))
    (A : ℕ → Finset (Fin (2*k - 1)))
    (ha : ∀ S : Finset (Fin (2*k - 1)), S.card = k → (S ∩ A (S ∩ P).card).Nonempty)
    (x : ℕ) (hx : x ≤ P.card) (hpk : P.card < k)
    (ap aq : ℕ)
    (hap : ap = (A x ∩ P).card)
    (haq : aq = (A x ∩ Pᶜ).card)
    (p q : ℕ) (hp : p = P.card) (hq : q = Pᶜ.card) :
    p + 1 ≤ ap + x ∨ q + 1 + x ≤ aq + k := by
  by_contra! h
  rcases h with ⟨h1, h2⟩
  have hP_sub : x ≤ (P \ A x).card := by
    rw [card_sdiff (s := A x) (t := P), ← hap, ← hp]
    omega
  have hQ_sub : k - x ≤ (Pᶜ \ A x).card := by
    rw [card_sdiff (s := A x) (t := Pᶜ), ← haq, ← hq]
    omega
  obtain ⟨SP, hSP_sub, hSP_card⟩ := exists_subset_card_eq hP_sub
  obtain ⟨SQ, hSQ_sub, hSQ_card⟩ := exists_subset_card_eq hQ_sub
  let S := SP ∪ SQ
  have hSP_P : SP ⊆ P := hSP_sub.trans sdiff_subset
  have hSQ_Q : SQ ⊆ Pᶜ := hSQ_sub.trans sdiff_subset
  have hdisj : Disjoint SP SQ := Disjoint.mono hSP_P hSQ_Q disjoint_compl_right
  have hScard : S.card = k := by
    dsimp [S]
    rw [card_union_of_disjoint hdisj, hSP_card, hSQ_card]
    omega
  have hS_inter_P : S ∩ P = SP := by
    ext a
    simp only [S, mem_inter, mem_union]
    constructor
    · rintro ⟨h | h, haP⟩
      · exact h
      · have := hSQ_Q h
        simp only [mem_compl] at this
        exact (this haP).elim
    · intro h
      exact ⟨Or.inl h, hSP_P h⟩
  have hS_inter_Ax : S ∩ A x = ∅ := by
    have hSP_A : SP ∩ A x = ∅ := by
      rw [← disjoint_iff_inter_eq_empty]
      exact Disjoint.mono_left hSP_sub disjoint_sdiff_self_left
    have hSQ_A : SQ ∩ A x = ∅ := by
      rw [← disjoint_iff_inter_eq_empty]
      exact Disjoint.mono_left hSQ_sub disjoint_sdiff_self_left
    dsimp [S]
    rw [union_inter_distrib_right, hSP_A, hSQ_A, union_empty]
  have hS_nonempty := ha S hScard
  rw [hS_inter_P, hSP_card] at hS_nonempty
  rw [nonempty_iff_ne_empty] at hS_nonempty
  exact hS_nonempty hS_inter_Ax

lemma op861_two_block_eligibility_collision_qsep_step (k : ℕ) (hk : 2 ≤ k)
    (P : Finset (Fin (2*k - 1))) (hpk : P.card < k)
    (A B : ℕ → Finset (Fin (2*k - 1)))
    (h_neg : ∀ S T : Finset (Fin (2*k - 1)), S.card = k → T.card = k → (S ∩ T).card = 1 →
      ¬ ((S ∩ A (S ∩ P).card) ∩ (T ∩ B (T ∩ P).card)).Nonempty)
    (x z : ℕ) (_hx : x ≤ P.card) (_hz : z ≤ P.card) (hxz : x + z = P.card)
    (c : Fin (2*k - 1)) (hcP : c ∈ Pᶜ) (hcA : c ∈ A x) (hcB : c ∈ B z) :
    False := by
  have hPcard : P.card + Pᶜ.card = 2 * k - 1 := by
    rw [card_compl, Fintype.card_fin]
    omega
  have hQc_card : (Pᶜ \ {c}).card = (k - x - 1) + (k - z - 1) := by
    rw [card_sdiff (s := {c}) (t := Pᶜ)]
    have : {c} ∩ Pᶜ = {c} := inter_eq_left.mpr (singleton_subset_iff.mpr hcP)
    rw [this, card_singleton]
    omega
  obtain ⟨PS, PT, hP_disj, hP_union, hPS_card, hPT_card⟩ :=
    op861_two_block_eligibility_collision_finset_partition_two P x z hxz.symm
  obtain ⟨QS, QT, hQ_disj, hQ_union, hQS_card, hQT_card⟩ :=
    op861_two_block_eligibility_collision_finset_partition_two (Pᶜ \ {c}) (k - x - 1) (k - z - 1) hQc_card
  have hPS_P : PS ⊆ P := by rw [← hP_union]; exact subset_union_left
  have hPT_P : PT ⊆ P := by rw [← hP_union]; exact subset_union_right
  have hQS_Qc : QS ⊆ Pᶜ \ {c} := by rw [← hQ_union]; exact subset_union_left
  have hQT_Qc : QT ⊆ Pᶜ \ {c} := by rw [← hQ_union]; exact subset_union_right
  have hQS_Q : QS ⊆ Pᶜ := hQS_Qc.trans sdiff_subset
  have hQT_Q : QT ⊆ Pᶜ := hQT_Qc.trans sdiff_subset
  have hc_notin_QS : c ∉ QS := fun h => (mem_sdiff.mp (hQS_Qc h)).2 (mem_singleton_self c)
  have hc_notin_QT : c ∉ QT := fun h => (mem_sdiff.mp (hQT_Qc h)).2 (mem_singleton_self c)
  let S := PS ∪ insert c QS
  let T := PT ∪ insert c QT
  have hS_card : S.card = k := by
    dsimp [S]
    have h1 : Disjoint PS (insert c QS) := by
      refine Disjoint.mono hPS_P ?_ disjoint_compl_right
      intro a ha
      simp only [mem_insert] at ha
      rcases ha with rfl | ha
      · exact hcP
      · exact hQS_Q ha
    rw [card_union_of_disjoint h1, card_insert_of_notMem hc_notin_QS, hPS_card, hQS_card]
    omega
  have hT_card : T.card = k := by
    dsimp [T]
    have h1 : Disjoint PT (insert c QT) := by
      refine Disjoint.mono hPT_P ?_ disjoint_compl_right
      intro a ha
      simp only [mem_insert] at ha
      rcases ha with rfl | ha
      · exact hcP
      · exact hQT_Q ha
    rw [card_union_of_disjoint h1, card_insert_of_notMem hc_notin_QT, hPT_card, hQT_card]
    omega
  have hS_inter_P : S ∩ P = PS := by
    ext a
    simp only [S, mem_inter, mem_union, mem_insert]
    constructor
    · rintro ⟨ha | rfl | ha, haP⟩
      · exact ha
      · exact (mem_compl.mp hcP haP).elim
      · exact (mem_compl.mp (hQS_Q ha) haP).elim
    · intro ha
      exact ⟨Or.inl ha, hPS_P ha⟩
  have hT_inter_P : T ∩ P = PT := by
    ext a
    simp only [T, mem_inter, mem_union, mem_insert]
    constructor
    · rintro ⟨ha | rfl | ha, haP⟩
      · exact ha
      · exact (mem_compl.mp hcP haP).elim
      · exact (mem_compl.mp (hQT_Q ha) haP).elim
    · intro ha
      exact ⟨Or.inl ha, hPT_P ha⟩
  have hST : S ∩ T = {c} := by
    ext a
    simp only [S, T, mem_inter, mem_union, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hS, hT⟩
      by_cases haP : a ∈ P
      · have haPS : a ∈ PS := by
          rcases hS with ha | rfl | ha
          · exact ha
          · exact (mem_compl.mp hcP haP).elim
          · exact (mem_compl.mp (hQS_Q ha) haP).elim
        have haPT : a ∈ PT := by
          rcases hT with ha | rfl | ha
          · exact ha
          · exact (mem_compl.mp hcP haP).elim
          · exact (mem_compl.mp (hQT_Q ha) haP).elim
        exact (Finset.disjoint_left.mp hP_disj haPS haPT).elim
      · have ha_compl : a ∈ Pᶜ := mem_compl.mpr haP
        rcases hS with ha | rfl | ha
        · exact (haP (hPS_P ha)).elim
        · rfl
        · rcases hT with ha' | rfl | ha'
          · exact (haP (hPT_P ha')).elim
          · rfl
          · exact (Finset.disjoint_left.mp hQ_disj ha ha').elim
    · rintro rfl
      simp
  have hST_card : (S ∩ T).card = 1 := by rw [hST, card_singleton]
  have hS_c : c ∈ S ∩ A (S ∩ P).card := by
    rw [hS_inter_P, hPS_card]
    exact mem_inter.mpr ⟨by simp [S], hcA⟩
  have hT_c : c ∈ T ∩ B (T ∩ P).card := by
    rw [hT_inter_P, hPT_card]
    exact mem_inter.mpr ⟨by simp [T], hcB⟩
  have h_col : ((S ∩ A (S ∩ P).card) ∩ (T ∩ B (T ∩ P).card)).Nonempty := ⟨c, mem_inter.mpr ⟨hS_c, hT_c⟩⟩
  exact h_neg S T hS_card hT_card hST_card h_col

lemma op861_two_block_eligibility_collision_psep_step (k : ℕ) (hk : 2 ≤ k)
    (P : Finset (Fin (2*k - 1))) (hpk : P.card < k)
    (A B : ℕ → Finset (Fin (2*k - 1)))
    (h_neg : ∀ S T : Finset (Fin (2*k - 1)), S.card = k → T.card = k → (S ∩ T).card = 1 →
      ¬ ((S ∩ A (S ∩ P).card) ∩ (T ∩ B (T ∩ P).card)).Nonempty)
    (x z : ℕ) (hx : x ≤ P.card) (hz : z ≤ P.card) (hxz : x + z = P.card + 1)
    (c : Fin (2*k - 1)) (hcP : c ∈ P) (hcA : c ∈ A x) (hcB : c ∈ B z) :
    False := by
  have hPcard : P.card + Pᶜ.card = 2 * k - 1 := by
    rw [card_compl, Fintype.card_fin]
    omega
  have hPc_card : (P \ {c}).card = (x - 1) + (z - 1) := by
    rw [card_sdiff (s := {c}) (t := P)]
    have : {c} ∩ P = {c} := inter_eq_left.mpr (singleton_subset_iff.mpr hcP)
    rw [this, card_singleton]
    omega
  have hQ_card : Pᶜ.card = (k - x) + (k - z) := by
    omega
  obtain ⟨PS, PT, hP_disj, hP_union, hPS_card, hPT_card⟩ :=
    op861_two_block_eligibility_collision_finset_partition_two (P \ {c}) (x - 1) (z - 1) hPc_card
  obtain ⟨QS, QT, hQ_disj, hQ_union, hQS_card, hQT_card⟩ :=
    op861_two_block_eligibility_collision_finset_partition_two Pᶜ (k - x) (k - z) hQ_card
  have hPS_Pc : PS ⊆ P \ {c} := by rw [← hP_union]; exact subset_union_left
  have hPT_Pc : PT ⊆ P \ {c} := by rw [← hP_union]; exact subset_union_right
  have hPS_P : PS ⊆ P := hPS_Pc.trans sdiff_subset
  have hPT_P : PT ⊆ P := hPT_Pc.trans sdiff_subset
  have hQS_Q : QS ⊆ Pᶜ := by rw [← hQ_union]; exact subset_union_left
  have hQT_Q : QT ⊆ Pᶜ := by rw [← hQ_union]; exact subset_union_right
  have hc_notin_PS : c ∉ PS := fun h => (mem_sdiff.mp (hPS_Pc h)).2 (mem_singleton_self c)
  have hc_notin_PT : c ∉ PT := fun h => (mem_sdiff.mp (hPT_Pc h)).2 (mem_singleton_self c)
  let S := insert c PS ∪ QS
  let T := insert c PT ∪ QT
  have hS_card : S.card = k := by
    dsimp [S]
    have h1 : Disjoint (insert c PS) QS := by
      refine Disjoint.mono ?_ hQS_Q disjoint_compl_right
      intro a ha
      simp only [mem_insert] at ha
      rcases ha with rfl | ha
      · exact hcP
      · exact hPS_P ha
    rw [card_union_of_disjoint h1, card_insert_of_notMem hc_notin_PS, hPS_card, hQS_card]
    omega
  have hT_card : T.card = k := by
    dsimp [T]
    have h1 : Disjoint (insert c PT) QT := by
      refine Disjoint.mono ?_ hQT_Q disjoint_compl_right
      intro a ha
      simp only [mem_insert] at ha
      rcases ha with rfl | ha
      · exact hcP
      · exact hPT_P ha
    rw [card_union_of_disjoint h1, card_insert_of_notMem hc_notin_PT, hPT_card, hQT_card]
    omega
  have hS_inter_P : S ∩ P = insert c PS := by
    ext a
    simp only [S, mem_inter, mem_union, mem_insert]
    constructor
    · rintro ⟨(rfl | ha) | ha, haP⟩
      · exact Or.inl rfl
      · exact Or.inr ha
      · exact (mem_compl.mp (hQS_Q ha) haP).elim
    · rintro (rfl | ha)
      · exact ⟨Or.inl (Or.inl rfl), hcP⟩
      · exact ⟨Or.inl (Or.inr ha), hPS_P ha⟩
  have hT_inter_P : T ∩ P = insert c PT := by
    ext a
    simp only [T, mem_inter, mem_union, mem_insert]
    constructor
    · rintro ⟨(rfl | ha) | ha, haP⟩
      · exact Or.inl rfl
      · exact Or.inr ha
      · exact (mem_compl.mp (hQT_Q ha) haP).elim
    · rintro (rfl | ha)
      · exact ⟨Or.inl (Or.inl rfl), hcP⟩
      · exact ⟨Or.inl (Or.inr ha), hPT_P ha⟩
  have hST : S ∩ T = {c} := by
    ext a
    simp only [S, T, mem_inter, mem_union, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hS, hT⟩
      by_cases haP : a ∈ P
      · rcases hS with (rfl | ha) | ha
        · rfl
        · rcases hT with (rfl | ha') | ha'
          · rfl
          · exact (Finset.disjoint_left.mp hP_disj ha ha').elim
          · exact (mem_compl.mp (hQT_Q ha') haP).elim
        · exact (mem_compl.mp (hQS_Q ha) haP).elim
      · have ha_compl : a ∈ Pᶜ := mem_compl.mpr haP
        rcases hS with (rfl | ha) | ha
        · exact (haP hcP).elim
        · exact (haP (hPS_P ha)).elim
        · rcases hT with (rfl | ha') | ha'
          · exact (haP hcP).elim
          · exact (haP (hPT_P ha')).elim
          · exact (Finset.disjoint_left.mp hQ_disj ha ha').elim
    · rintro rfl
      simp
  have hST_card : (S ∩ T).card = 1 := by rw [hST, card_singleton]
  have hS_c : c ∈ S ∩ A (S ∩ P).card := by
    rw [hS_inter_P, card_insert_of_notMem hc_notin_PS, hPS_card]
    have : x - 1 + 1 = x := by omega
    rw [this]
    exact mem_inter.mpr ⟨by simp [S], hcA⟩
  have hT_c : c ∈ T ∩ B (T ∩ P).card := by
    rw [hT_inter_P, card_insert_of_notMem hc_notin_PT, hPT_card]
    have : z - 1 + 1 = z := by omega
    rw [this]
    exact mem_inter.mpr ⟨by simp [T], hcB⟩
  have h_col : ((S ∩ A (S ∩ P).card) ∩ (T ∩ B (T ∩ P).card)).Nonempty := ⟨c, mem_inter.mpr ⟨hS_c, hT_c⟩⟩
  exact h_neg S T hS_card hT_card hST_card h_col

theorem op861_two_block_eligibility_collision (k : ℕ) (hk : 2 ≤ k)
    (P : Finset (Fin (2*k - 1))) (hp : 0 < P.card) (hpk : P.card < k)
    (A B : ℕ → Finset (Fin (2*k - 1)))
    (ha : ∀ S : Finset (Fin (2*k - 1)), S.card = k →
      (S ∩ A (S ∩ P).card).Nonempty)
    (hb : ∀ S : Finset (Fin (2*k - 1)), S.card = k →
      (S ∩ B (S ∩ P).card).Nonempty) :
    ∃ S T : Finset (Fin (2*k - 1)), S.card = k ∧ T.card = k ∧
      (S ∩ T).card = 1 ∧
      ((S ∩ A (S ∩ P).card) ∩ (T ∩ B (T ∩ P).card)).Nonempty := by
  by_contra h_neg
  have h_neg' : ∀ S T : Finset (Fin (2*k - 1)), S.card = k → T.card = k → (S ∩ T).card = 1 →
      ¬ ((S ∩ A (S ∩ P).card) ∩ (T ∩ B (T ∩ P).card)).Nonempty := by
    intro S T hS hT hST hcol
    exact h_neg ⟨S, T, hS, hT, hST, hcol⟩
  let p := P.card
  let q := Pᶜ.card
  have hp_ge : 1 ≤ p := by omega
  have hpq : p + q + 1 = 2 * k := by
    have h : p + q = 2 * k - 1 := by
      dsimp [p, q]
      rw [card_compl, Fintype.card_fin]
      omega
    omega
  let ap (x : ℕ) : ℕ := (A x ∩ P).card
  let aq (x : ℕ) : ℕ := (A x ∩ Pᶜ).card
  let bp (x : ℕ) : ℕ := (B x ∩ P).card
  let bq (x : ℕ) : ℕ := (B x ∩ Pᶜ).card
  have hbound : ∀ x ≤ p, ap x ≤ p ∧ bp x ≤ p := by
    intro x _
    exact ⟨card_le_card inter_subset_right, card_le_card inter_subset_right⟩
  have ha_obs : ∀ x ≤ p, p + 1 ≤ ap x + x ∨ q + 1 + x ≤ aq x + k := by
    intro x hx
    exact op861_two_block_eligibility_collision_ha_step k P A ha x hx hpk (ap x) (aq x) rfl rfl p q rfl rfl
  have hb_obs : ∀ x ≤ p, p + 1 ≤ bp x + x ∨ q + 1 + x ≤ bq x + k := by
    intro x hx
    exact op861_two_block_eligibility_collision_ha_step k P B hb x hx hpk (bp x) (bq x) rfl rfl p q rfl rfl
  have hqsep : ∀ x z, x ≤ p → z ≤ p → x + z = p → aq x + bq z ≤ q := by
    intro x z hx hz hxz
    by_cases hdisj : Disjoint (A x ∩ Pᶜ) (B z ∩ Pᶜ)
    · rw [← card_union_of_disjoint hdisj]
      exact card_le_card (union_subset inter_subset_right inter_subset_right)
    · obtain ⟨c, hc1, hc2⟩ := not_disjoint_iff.mp hdisj
      have hcP : c ∈ Pᶜ := (mem_inter.mp hc1).2
      have hcA : c ∈ A x := (mem_inter.mp hc1).1
      have hcB : c ∈ B z := (mem_inter.mp hc2).1
      exact False.elim (op861_two_block_eligibility_collision_qsep_step k hk P hpk A B h_neg' x z hx hz hxz c hcP hcA hcB)
  have hpsep : ∀ x z, x ≤ p → z ≤ p → x + z = p + 1 → ap x + bp z ≤ p := by
    intro x z hx hz hxz
    by_cases hdisj : Disjoint (A x ∩ P) (B z ∩ P)
    · rw [← card_union_of_disjoint hdisj]
      exact card_le_card (union_subset inter_subset_right inter_subset_right)
    · obtain ⟨c, hc1, hc2⟩ := not_disjoint_iff.mp hdisj
      have hcP : c ∈ P := (mem_inter.mp hc1).2
      have hcA : c ∈ A x := (mem_inter.mp hc1).1
      have hcB : c ∈ B z := (mem_inter.mp hc2).1
      exact False.elim (op861_two_block_eligibility_collision_psep_step k hk P hpk A B h_neg' x z hx hz hxz c hcP hcA hcB)
  exact op861_partition_profile_obstruction k p q hp_ge hpk hpq ap aq bp bq hbound ha_obs hb_obs hqsep hpsep
