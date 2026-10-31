import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetCoverRankRelation

/-!
# condorcet_small_complement_fractional_cover

Topic: social_choice   Node: 01bb56b6a529

Provenance: helper lemma. IN-391, OP-19 campaign session10, 2026-10-30. Supporting lemmas and precisely scoped method diagnostics for the rank-saturated acyclic-cover route. The main election theorem remains open; no new election bound or novelty is claimed.

For k at least two, let a finite nonnegative real-weighted family of subsets have unit weighted coverage at every element of a specified finite set T. Suppose each positive-weight member misses at most k elements of T, and the total weight is strictly less than k+1. Then at most k positive-weight members cover T.
-/

open Finset BigOperators

theorem condorcet_choose_cov_on {m n : ℕ} [Nonempty (Fin m)] (T : Finset (Fin n))
    (A : Fin m → Finset (Fin n)) (w : Fin m → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hload : ∀ v ∈ T, (∑ a : Fin m, if v ∈ A a then w a else 0) = 1)
    (S : Finset (Fin n)) (hST : S ⊆ T) :
    ∃ f : Fin n → Fin m, (∀ v ∈ S, 0 < w (f v) ∧ v ∈ A (f v)) := by
  have h_ex : ∀ v : Fin n, ∃ a : Fin m, v ∈ S → 0 < w a ∧ v ∈ A a := by
    intro v
    by_cases hv : v ∈ S
    · have h_sum := hload v (hST hv)
      have : ∃ a : Fin m, 0 < w a ∧ v ∈ A a := by
        by_contra h_none
        have h_zero : (∑ a : Fin m, if v ∈ A a then w a else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro a _
          split_ifs with h_in
          · have hwa : w a = 0 := by
              have h_not : ¬ (0 < w a ∧ v ∈ A a) := fun h => h_none ⟨a, h⟩
              have h_not_pos : ¬ (0 < w a) := fun hp => h_not ⟨hp, h_in⟩
              have := hw a
              linarith
            exact hwa
          · rfl
        linarith
      rcases this with ⟨a, ha⟩
      exact ⟨a, fun _ => ha⟩
    · exact ⟨Classical.arbitrary (Fin m), fun h => (hv h).elim⟩
  choose f hf using h_ex
  exact ⟨f, fun v hv => hf v hv⟩

theorem condorcet_sum_double_inter {m n : ℕ} (S : Finset (Fin n)) (A : Fin m → Finset (Fin n))
    (w : Fin m → ℝ) :
    (∑ v ∈ S, ∑ a : Fin m, if v ∈ A a then w a else 0) =
      ∑ a : Fin m, w a * (S ∩ A a).card := by
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [← sum_filter]
  have : (filter (fun v => v ∈ A a) S) = S ∩ A a := by
    ext v
    simp [mem_inter]
  rw [this, sum_const, nsmul_eq_mul]
  ring

theorem condorcet_small_complement_fractional_cover {m n k : ℕ} (hk : 2 ≤ k)
    (T : Finset (Fin n)) (A : Fin m → Finset (Fin n)) (w : Fin m → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hmiss : ∀ a, 0 < w a → (T \ A a).card ≤ k)
    (hload : ∀ v ∈ T, (∑ a : Fin m, if v ∈ A a then w a else 0) = 1)
    (hmass : (∑ a : Fin m, w a) < (k + 1 : ℕ)) :
    ∃ J : Finset (Fin m), J.card ≤ k ∧ (∀ a ∈ J, 0 < w a) ∧
      ∀ v ∈ T, ∃ a ∈ J, v ∈ A a := by
  by_cases hT : T.card ≤ k
  · by_cases h_emp : T = ∅
    · use ∅
      refine ⟨by simp, fun a ha => by simp at ha, fun v hv => by simp [h_emp] at hv⟩
    · have hT_nonempty : T.Nonempty := nonempty_iff_ne_empty.mpr h_emp
      rcases hT_nonempty with ⟨v0, hv0⟩
      have : Nonempty (Fin m) := by
        have h := hload v0 hv0
        by_contra h_empty
        have hm0 : IsEmpty (Fin m) := not_nonempty_iff.mp h_empty
        have : (∑ a : Fin m, if v0 ∈ A a then w a else 0) = 0 := Finset.sum_of_isEmpty _
        linarith
      rcases condorcet_choose_cov_on T A w hw hload T subset_rfl with ⟨f, hf⟩
      use T.image f
      refine ⟨by have := card_image_le (s := T) (f := f); omega, ?_, ?_⟩
      · intro x hx
        rcases mem_image.mp hx with ⟨v, hv, rfl⟩
        exact (hf v hv).1
      · intro v hv
        exact ⟨f v, mem_image_of_mem f hv, (hf v hv).2⟩
  · have hT_gt : k < T.card := not_le.mp hT
    have hT_nonempty : T.Nonempty := by
      by_contra hc
      have : T = ∅ := not_nonempty_iff_eq_empty.mp hc
      subst this
      simp at hT_gt
    rcases hT_nonempty with ⟨v0, hv0⟩
    have : Nonempty (Fin m) := by
      have h := hload v0 hv0
      by_contra h_empty
      have hm0 : IsEmpty (Fin m) := not_nonempty_iff.mp h_empty
      have : (∑ a : Fin m, if v0 ∈ A a then w a else 0) = 0 := Finset.sum_of_isEmpty _
      linarith
    by_cases h_less : ∃ a, 0 < w a ∧ (T \ A a).card ≤ k - 1
    · rcases h_less with ⟨a, hwa, hR⟩
      rcases condorcet_choose_cov_on T A w hw hload (T \ A a) sdiff_subset with ⟨f, hf⟩
      let J := insert a ((T \ A a).image f)
      use J
      refine ⟨?_, ?_, ?_⟩
      · dsimp [J]
        have h1 := card_insert_le a ((T \ A a).image f)
        have h2 := card_image_le (s := T \ A a) (f := f)
        omega
      · intro x hx
        simp only [J, mem_insert, mem_image] at hx
        rcases hx with rfl | ⟨v, hv, rfl⟩
        · exact hwa
        · exact (hf v hv).1
      · intro v hv
        by_cases h : v ∈ A a
        · exact ⟨a, mem_insert_self a _, h⟩
        · have hmem : v ∈ T \ A a := mem_sdiff.mpr ⟨hv, h⟩
          refine ⟨f v, mem_insert_of_mem (mem_image_of_mem f hmem), (hf v hmem).2⟩
    · have h_not_less : ∀ a, 0 < w a → k - 1 < (T \ A a).card := by
        intro a ha
        by_contra hc
        exact h_less ⟨a, ha, not_lt.mp hc⟩
      by_cases h_pair : ∃ a b, 0 < w a ∧ 0 < w b ∧ 2 ≤ ((T \ A a) ∩ A b).card
      · rcases h_pair with ⟨a, b, hwa, hwb, h_inter⟩
        rcases condorcet_choose_cov_on T A w hw hload ((T \ A a) \ A b)
          (subset_trans sdiff_subset sdiff_subset) with ⟨f, hf⟩
        let J := insert a (insert b (((T \ A a) \ A b).image f))
        use J
        have hR_card : ((T \ A a) \ A b).card ≤ k - 2 := by
          have hS_card : (T \ A a).card ≤ k := hmiss a hwa
          rw [card_sdiff, inter_comm]
          omega
        refine ⟨?_, ?_, ?_⟩
        · dsimp [J]
          have h1 := card_insert_le a (insert b (((T \ A a) \ A b).image f))
          have h2 := card_insert_le b (((T \ A a) \ A b).image f)
          have h3 := card_image_le (s := (T \ A a) \ A b) (f := f)
          omega
        · intro x hx
          simp only [J, mem_insert, mem_image] at hx
          rcases hx with rfl | rfl | ⟨v, hv, rfl⟩
          · exact hwa
          · exact hwb
          · exact (hf v hv).1
        · intro v hv
          by_cases ha : v ∈ A a
          · exact ⟨a, mem_insert_self a _, ha⟩
          · by_cases hb : v ∈ A b
            · exact ⟨b, mem_insert_of_mem (mem_insert_self b _), hb⟩
            · have hmem : v ∈ (T \ A a) \ A b := by
                rw [mem_sdiff, mem_sdiff]
                exact ⟨⟨hv, ha⟩, hb⟩
              refine ⟨f v, mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem f hmem)), (hf v hmem).2⟩
      · have h_not_pair : ∀ a b, 0 < w a → 0 < w b → ((T \ A a) ∩ A b).card < 2 := by
          intro a b ha hb
          by_contra hc
          exact h_pair ⟨a, b, ha, hb, not_lt.mp hc⟩
        have h_eq_k : ∀ a, 0 < w a → (T \ A a).card = k := by
          intro a ha
          have h1 := hmiss a ha
          have h2 := h_not_less a ha
          omega
        have h_inter_le : ∀ a b, 0 < w a → 0 < w b → ((T \ A a) ∩ A b).card ≤ 1 := by
          intro a b ha hb
          have := h_not_pair a b ha hb
          omega
        have h_sum_v0 := hload v0 hv0
        have h_ex_a : ∃ a, 0 < w a := by
          by_contra hc
          have h_zero : (∑ a : Fin m, if v0 ∈ A a then w a else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro a _
            split_ifs
            · have : ¬ (0 < w a) := fun hp => hc ⟨a, hp⟩
              have : w a = 0 := by linarith [hw a]
              exact this
            · rfl
          linarith
        rcases h_ex_a with ⟨a, hwa⟩
        have h_sum_sdiff : ((T \ A a).card : ℝ) = ∑ b : Fin m, w b * ((T \ A a) ∩ A b).card := by
          have h1 : (∑ v ∈ T \ A a, ∑ b : Fin m, if v ∈ A b then w b else 0) =
              ∑ b : Fin m, w b * ((T \ A a) ∩ A b).card := condorcet_sum_double_inter (T \ A a) A w
          have h2 : (∑ v ∈ T \ A a, ∑ b : Fin m, if v ∈ A b then w b else 0) =
              ∑ v ∈ T \ A a, (1 : ℝ) := by
            apply sum_congr rfl
            intro v hv
            exact hload v (mem_sdiff.mp hv).1
          rw [h2, sum_const, nsmul_eq_mul, mul_one] at h1
          exact h1
        have h_card_sdiff_k : ((T \ A a).card : ℝ) = (k : ℝ) := by
          rw [h_eq_k a hwa]
        rw [h_card_sdiff_k] at h_sum_sdiff
        have h_bound : (∑ b : Fin m, w b * ((T \ A a) ∩ A b).card) ≤ (∑ b : Fin m, w b) - w a := by
          have h_disj : (T \ A a) ∩ A a = ∅ := by
            ext v
            simp
          have h_card_a : (((T \ A a) ∩ A a).card : ℝ) = 0 := by simp [h_disj]
          have h_le : ∀ b : Fin m, b ≠ a → w b * ((T \ A a) ∩ A b).card ≤ w b := by
            intro b _
            by_cases hwb : 0 < w b
            · have h1 : (((T \ A a) ∩ A b).card : ℝ) ≤ 1 := by
                exact_mod_cast (h_inter_le a b hwa hwb)
              nlinarith [hw b]
            · have : w b = 0 := by linarith [hw b]
              simp [this]
          have h_sum : (∑ b : Fin m, w b * ((T \ A a) ∩ A b).card) =
              w a * (((T \ A a) ∩ A a).card : ℝ) + ∑ b ∈ univ.erase a, w b * ((T \ A a) ∩ A b).card := by
            exact (Finset.add_sum_erase univ (fun b => w b * ((T \ A a) ∩ A b).card) (mem_univ a)).symm
          rw [h_sum, h_card_a, mul_zero, zero_add]
          have h_erase : (∑ b ∈ univ.erase a, w b * ((T \ A a) ∩ A b).card) ≤ ∑ b ∈ univ.erase a, w b := by
            apply sum_le_sum
            intro b hb
            exact h_le b (mem_erase.mp hb).1
          have h_orig : (∑ b ∈ univ.erase a, w b) = (∑ b : Fin m, w b) - w a := by
            have := (Finset.add_sum_erase univ w (mem_univ a)).symm
            linarith
          linarith
        have h_gt_k : (k : ℝ) < ∑ b : Fin m, w b := by
          linarith [h_sum_sdiff, h_bound]
        have hkT : k ≤ T.card := by omega
        have h_sum_T : (T.card : ℝ) = (∑ b : Fin m, w b) * (T.card - k : ℝ) := by
          have h1 : (∑ v ∈ T, ∑ b : Fin m, if v ∈ A b then w b else 0) =
              ∑ b : Fin m, w b * (T ∩ A b).card := condorcet_sum_double_inter T A w
          have h2 : (∑ v ∈ T, ∑ b : Fin m, if v ∈ A b then w b else 0) =
              ∑ v ∈ T, (1 : ℝ) := by
            apply sum_congr rfl
            intro v hv
            exact hload v hv
          rw [h2, sum_const, nsmul_eq_mul, mul_one] at h1
          have h3 : ∀ b : Fin m, w b * (T ∩ A b).card = w b * (T.card - k : ℝ) := by
            intro b
            by_cases hwb : w b = 0
            · simp [hwb]
            · have hpos : 0 < w b := lt_of_le_of_ne (hw b) (Ne.symm hwb)
              have hcard : (T ∩ A b).card = T.card - k := by
                have hsdiff : (T \ A b).card = k := h_eq_k b hpos
                have h_inter : (T ∩ A b).card = T.card - (T \ A b).card := by
                  have h_sub : T ∩ A b = T \ (T \ A b) := by
                    ext x
                    simp only [mem_inter, mem_sdiff]
                    tauto
                  rw [h_sub, card_sdiff_of_subset sdiff_subset]
                omega
              rw [hcard, Nat.cast_sub hkT]
          have h4 : (∑ b : Fin m, w b * (T ∩ A b).card) = ∑ b : Fin m, w b * (T.card - k : ℝ) := by
            apply sum_congr rfl
            intro b _
            exact h3 b
          rw [h4, ← sum_mul] at h1
          exact h1
        by_cases ht_eq : T.card = k + 1
        · have h_sub_1 : (T.card - k : ℝ) = 1 := by
            rw [ht_eq]
            push_cast
            ring
          rw [h_sub_1, mul_one] at h_sum_T
          have hmass_real : (∑ a : Fin m, w a) < (k + 1 : ℝ) := by
            exact_mod_cast hmass
          rw [← h_sum_T, ht_eq] at hmass_real
          push_cast at hmass_real
          linarith
        · have ht_ge : k + 2 ≤ T.card := by omega
          have hk_pos : (0 : ℝ) < (T.card - k : ℝ) := by
            have : (k : ℝ) + 2 ≤ (T.card : ℝ) := by exact_mod_cast ht_ge
            linarith
          have h_le_k : (∑ b : Fin m, w b) ≤ (k : ℝ) := by
            have h2 : (T.card : ℝ) ≤ (k : ℝ) * (T.card - k : ℝ) := by
              have : (k : ℝ) + 2 ≤ (T.card : ℝ) := by exact_mod_cast ht_ge
              have hk_ge_2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
              nlinarith
            nth_rw 1 [h_sum_T] at h2
            exact (mul_le_mul_iff_of_pos_right hk_pos).mp h2
          linarith
