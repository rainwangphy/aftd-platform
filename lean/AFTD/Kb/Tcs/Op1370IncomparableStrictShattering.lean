import AFTD.Prelude

/-!
# op_1370_incomparable_strict_shattering

Topic: combinatorics   Node: 40db89764e74

Provenance: helper lemma. Consequence of the isometric inclusion-graph property of shattering-extremal systems, https://www.combinatorics.org/ojs/index.php/eljc/article/download/v21i4p30/pdf/, Proposition 12; used in the private-element case of OP-1370.

The union of two nonempty mutually strongly incomparable finite set families shatters strictly more sets than it contains.
-/

open Finset
set_option maxHeartbeats 800000

lemma op1370_shatter_no_member {α : Type*} [DecidableEq α]
    (a : α) (𝒜 : Finset (Finset α))
    (h : ∀ t ∈ 𝒜, a ∉ t) {s : Finset α} (hs : 𝒜.Shatters s) : a ∉ s := by
  obtain ⟨u, hu, hsu⟩ := hs.exists_superset
  exact notMem_mono hsu (h u hu)

lemma op1370_shatter_fibers (α : Type*) [DecidableEq α] (a : α)
    (U : Finset (Finset α)) :
    (U.nonMemberSubfamily a ∪ U.memberSubfamily a).shatterer.card +
      ((U.nonMemberSubfamily a).shatterer ∩ (U.memberSubfamily a).shatterer).card ≤ U.shatterer.card := by
  classical
  let U0 := U.nonMemberSubfamily a
  let U1 := U.memberSubfamily a
  let P := (U0 ∪ U1).shatterer
  let Q := (U0.shatterer ∩ U1.shatterer).image (insert a)
  have h0 : ∀ t ∈ U0 ∪ U1, a ∉ t := by
    intro t ht
    rcases mem_union.mp ht with ht | ht
    · exact (mem_nonMemberSubfamily.mp ht).2
    · exact (mem_memberSubfamily.mp ht).2
  have hP0 : ∀ s ∈ P, a ∉ s := by
    intro s hs
    exact op1370_shatter_no_member a _ h0 (mem_shatterer.mp hs)
  have hQcard : Q.card = (U0.shatterer ∩ U1.shatterer).card := by
    apply card_image_of_injOn
    intro s hs t ht he
    have hsa : a ∉ s := op1370_shatter_no_member a _ (fun x hx => (mem_nonMemberSubfamily.mp hx).2) (mem_shatterer.mp (mem_inter.mp hs).1)
    have hta : a ∉ t := op1370_shatter_no_member a _ (fun x hx => (mem_nonMemberSubfamily.mp hx).2) (mem_shatterer.mp (mem_inter.mp ht).1)
    have := congrArg (fun v : Finset α => v.erase a) he
    simpa [hsa, hta] using this
  have hdis : Disjoint P Q := by
    rw [disjoint_left]
    intro s hs hq
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
    exact hP0 (insert a t) hs (mem_insert_self _ _)
  have hP : P ⊆ U.shatterer := by
    intro s hs
    have hs0 := hP0 s hs
    apply mem_shatterer.mpr
    intro t ht
    obtain ⟨v, hv, he⟩ := (mem_shatterer.mp hs) ht
    rcases mem_union.mp hv with hv | hv
    · exact ⟨v, (mem_nonMemberSubfamily.mp hv).1, he⟩
    · refine ⟨insert a v, (mem_memberSubfamily.mp hv).1, ?_⟩
      simpa [inter_insert_of_notMem hs0] using he
  have hQ : Q ⊆ U.shatterer := by
    intro s hs
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hs
    have hv0 := mem_shatterer.mp (mem_inter.mp hv).1
    have hv1 := mem_shatterer.mp (mem_inter.mp hv).2
    apply mem_shatterer.mpr
    intro t ht
    have htv : t.erase a ⊆ v := by
      intro z hz
      have hz' := ht (mem_of_mem_erase hz)
      simpa [(mem_erase.mp hz).1] using hz'
    by_cases ha : a ∈ t
    · obtain ⟨w, hw, he⟩ := hv1 htv
      refine ⟨insert a w, (mem_memberSubfamily.mp hw).1, ?_⟩
      ext z
      by_cases hza : z = a
      · subst z; simp [ha]
      · have hez := congrArg (fun q : Finset α => z ∈ q) he
        simp [hza] at hez ⊢
        exact hez
    · obtain ⟨w, hw, he⟩ := hv0 htv
      refine ⟨w, (mem_nonMemberSubfamily.mp hw).1, ?_⟩
      have hwa := (mem_nonMemberSubfamily.mp hw).2
      simpa [insert_inter_of_notMem hwa, erase_eq_self.mpr ha] using he
  have hh := card_le_card (union_subset hP hQ)
  rw [card_union_of_disjoint hdis, hQcard] at hh
  exact hh

lemma op1370_shatter_fiber_sum (α : Type*) [DecidableEq α] (a : α)
    (U : Finset (Finset α)) :
    (U.nonMemberSubfamily a).shatterer.card + (U.memberSubfamily a).shatterer.card ≤ U.shatterer.card := by
  have h := op1370_shatter_fibers α a U
  have h0 := card_union_add_card_inter ((U.nonMemberSubfamily a).shatterer) ((U.memberSubfamily a).shatterer)
  have hh : (U.nonMemberSubfamily a).shatterer ∪ (U.memberSubfamily a).shatterer ⊆
      (U.nonMemberSubfamily a ∪ U.memberSubfamily a).shatterer :=
    union_subset (shatterer_mono (subset_union_left)) (shatterer_mono (subset_union_right))
  have := card_le_card hh
  omega

lemma op1370_cross_disjoint_sections {α : Type*} [DecidableEq α] (a : α)
    (F G : Finset (Finset α))
    (hinc : ∀ A ∈ F, ∀ B ∈ G, ¬ A ⊆ B ∧ ¬ B ⊆ A) :
    Disjoint (F.nonMemberSubfamily a) (G.memberSubfamily a) := by
  classical
  rw [disjoint_left]
  intro s hs ht
  have hf := (mem_nonMemberSubfamily.mp hs).1
  have hg := (mem_memberSubfamily.mp ht).1
  exact (hinc s hf (insert a s) hg).1 (subset_insert a s)

lemma op1370_strict_shattering_aux {α : Type*} [DecidableEq α] (U : Finset (Finset α)) :
    ∀ F G : Finset (Finset α), U = F ∪ G → F.Nonempty → G.Nonempty →
      (∀ A ∈ F, ∀ B ∈ G, ¬ A ⊆ B ∧ ¬ B ⊆ A) → U.card < U.shatterer.card := by
  classical
  refine Finset.memberFamily_induction_on U ?_ ?_ ?_
  · intro F G hU hF hG hinc
    have : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs
      have : s ∈ (∅ : Finset (Finset α)) := by rw [hU]; exact mem_union_left _ hs
      simpa using this
    exact False.elim (hF.ne_empty this)
  · intro F G hU hF hG hinc
    obtain ⟨A, hA⟩ := hF
    obtain ⟨B, hB⟩ := hG
    have hA0 : A = ∅ := by
      have : A ∈ ({∅} : Finset (Finset α)) := by rw [hU]; exact mem_union_left _ hA
      simpa using this
    have hB0 : B = ∅ := by
      have : B ∈ ({∅} : Finset (Finset α)) := by rw [hU]; exact mem_union_right _ hB
      simpa using this
    subst A; subst B
    exact False.elim ((hinc ∅ hA ∅ hB).1 (subset_refl ∅))
  · intro a U ih0 ih1 F G hU hF hG hinc
    let F0 := F.nonMemberSubfamily a
    let F1 := F.memberSubfamily a
    let G0 := G.nonMemberSubfamily a
    let G1 := G.memberSubfamily a
    let U0 := U.nonMemberSubfamily a
    let U1 := U.memberSubfamily a
    have hu0 : U0 = F0 ∪ G0 := by simp [U0, F0, G0, hU, nonMemberSubfamily_union]
    have hu1 : U1 = F1 ∪ G1 := by simp [U1, F1, G1, hU, memberSubfamily_union]
    have hinc0 : ∀ A ∈ F0, ∀ B ∈ G0, ¬ A ⊆ B ∧ ¬ B ⊆ A := by
      intro A hA B hB
      exact hinc A (mem_nonMemberSubfamily.mp hA).1 B (mem_nonMemberSubfamily.mp hB).1
    have hinc1 : ∀ A ∈ F1, ∀ B ∈ G1, ¬ A ⊆ B ∧ ¬ B ⊆ A := by
      intro A hA B hB
      have h := hinc (insert a A) (mem_memberSubfamily.mp hA).1
        (insert a B) (mem_memberSubfamily.mp hB).1
      constructor <;> intro hs
      · exact h.1 (insert_subset_insert a hs)
      · exact h.2 (insert_subset_insert a hs)
    have hcards : U0.card + U1.card = U.card := by
      simpa [U0, U1, Nat.add_comm] using card_memberSubfamily_add_card_nonMemberSubfamily a U
    have hsh := op1370_shatter_fiber_sum α a U
    change U0.shatterer.card + U1.shatterer.card ≤ U.shatterer.card at hsh
    by_cases hf0 : F0.Nonempty
    · by_cases hg0 : G0.Nonempty
      · have h := ih0 F0 G0 hu0 hf0 hg0 hinc0
        change U0.card < U0.shatterer.card at h
        have h' := card_le_card_shatterer U1
        omega
      · by_cases hf1 : F1.Nonempty
        · have hg1 : G1.Nonempty := by
            by_contra hh
            have hz0 : G0 = ∅ := not_nonempty_iff_eq_empty.mp hg0
            have hz1 : G1 = ∅ := not_nonempty_iff_eq_empty.mp hh
            have hhg := card_memberSubfamily_add_card_nonMemberSubfamily a G
            change G1.card + G0.card = G.card at hhg
            simp [hz0, hz1] at hhg
            exact hG.ne_empty (card_eq_zero.mp hhg.symm)
          have h := ih1 F1 G1 hu1 hf1 hg1 hinc1
          change U1.card < U1.shatterer.card at h
          have h' := card_le_card_shatterer U0
          omega
        · have hG1 : G1.Nonempty := by
            by_contra hh
            have hz0 : G0 = ∅ := not_nonempty_iff_eq_empty.mp hg0
            have hz1 : G1 = ∅ := not_nonempty_iff_eq_empty.mp hh
            have hhg := card_memberSubfamily_add_card_nonMemberSubfamily a G
            change G1.card + G0.card = G.card at hhg
            simp [hz0, hz1] at hhg
            exact hG.ne_empty (card_eq_zero.mp hhg.symm)
          have hU0 : U0 = F0 := by rw [hu0, not_nonempty_iff_eq_empty.mp hg0, union_empty]
          have hU1 : U1 = G1 := by rw [hu1, not_nonempty_iff_eq_empty.mp hf1, empty_union]
          have hd : Disjoint U0 U1 := by
            rw [hU0, hU1]
            exact op1370_cross_disjoint_sections a F G hinc
          have hu0ne : U0.Nonempty := hU0 ▸ hf0
          have hu1ne : U1.Nonempty := hU1 ▸ hG1
          have hempty : (∅ : Finset α) ∈ U0.shatterer ∩ U1.shatterer := by
            simp [hu0ne, hu1ne]
          have hinter : 0 < (U0.shatterer ∩ U1.shatterer).card := card_pos.mpr ⟨∅, hempty⟩
          have hun := card_le_card_shatterer (U0 ∪ U1)
          rw [card_union_of_disjoint hd] at hun
          have hmore := op1370_shatter_fibers α a U
          change (U0 ∪ U1).shatterer.card + (U0.shatterer ∩ U1.shatterer).card ≤ U.shatterer.card at hmore
          omega
    · by_cases hg1 : G1.Nonempty
      · by_cases hf1 : F1.Nonempty
        · have h := ih1 F1 G1 hu1 hf1 hg1 hinc1
          change U1.card < U1.shatterer.card at h
          have h' := card_le_card_shatterer U0
          omega
        · have hF0 : F0.Nonempty := by
            by_contra hh
            have hz0 : F0 = ∅ := not_nonempty_iff_eq_empty.mp hh
            have hz1 : F1 = ∅ := not_nonempty_iff_eq_empty.mp hf1
            have hhf := card_memberSubfamily_add_card_nonMemberSubfamily a F
            change F1.card + F0.card = F.card at hhf
            simp [hz0, hz1] at hhf
            exact hF.ne_empty (card_eq_zero.mp hhf.symm)
          exact False.elim (hf0 hF0)
      · have hG0 : G0.Nonempty := by
          by_contra hh
          have hz0 : G0 = ∅ := not_nonempty_iff_eq_empty.mp hh
          have hz1 : G1 = ∅ := not_nonempty_iff_eq_empty.mp hg1
          have hhg := card_memberSubfamily_add_card_nonMemberSubfamily a G
          change G1.card + G0.card = G.card at hhg
          simp [hz0, hz1] at hhg
          exact hG.ne_empty (card_eq_zero.mp hhg.symm)
        have hF1 : F1.Nonempty := by
          by_contra hh
          have hz0 : F0 = ∅ := not_nonempty_iff_eq_empty.mp hf0
          have hz1 : F1 = ∅ := not_nonempty_iff_eq_empty.mp hh
          have hhf := card_memberSubfamily_add_card_nonMemberSubfamily a F
          change F1.card + F0.card = F.card at hhf
          simp [hz0, hz1] at hhf
          exact hF.ne_empty (card_eq_zero.mp hhf.symm)
        have hU0 : U0 = G0 := by rw [hu0, not_nonempty_iff_eq_empty.mp hf0, empty_union]
        have hU1 : U1 = F1 := by rw [hu1, not_nonempty_iff_eq_empty.mp hg1, union_empty]
        have hd : Disjoint U0 U1 := by
          rw [hU0, hU1]
          exact op1370_cross_disjoint_sections a G F (fun A hA B hB => ⟨(hinc B hB A hA).2, (hinc B hB A hA).1⟩)
        have hu0ne : U0.Nonempty := hU0 ▸ hG0
        have hu1ne : U1.Nonempty := hU1 ▸ hF1
        have hempty : (∅ : Finset α) ∈ U0.shatterer ∩ U1.shatterer := by simp [hu0ne, hu1ne]
        have hinter : 0 < (U0.shatterer ∩ U1.shatterer).card := card_pos.mpr ⟨∅, hempty⟩
        have hun := card_le_card_shatterer (U0 ∪ U1)
        rw [card_union_of_disjoint hd] at hun
        have hmore := op1370_shatter_fibers α a U
        change (U0 ∪ U1).shatterer.card + (U0.shatterer ∩ U1.shatterer).card ≤ U.shatterer.card at hmore
        omega

theorem op_1370_incomparable_strict_shattering {α : Type*} [DecidableEq α]
    (F G : Finset (Finset α)) (hF : F.Nonempty) (hG : G.Nonempty)
    (hinc : ∀ A ∈ F, ∀ B ∈ G, ¬ A ⊆ B ∧ ¬ B ⊆ A) :
    (F ∪ G).card < (F ∪ G).shatterer.card := by
  exact op1370_strict_shattering_aux (F ∪ G) F G rfl hF hG hinc
