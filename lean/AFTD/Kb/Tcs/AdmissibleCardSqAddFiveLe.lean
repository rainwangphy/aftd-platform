import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdmissible
import AFTD.Kb.Tcs.CardPowersetCardImageSumGe
import AFTD.Kb.Tcs.PairwiseDisjointKSumOfIsAdmissible
import AFTD.Kb.Tcs.SumLeCardMulOfSubsetIcc

/-!
# admissible_card_sq_add_five_le

Topic: combinatorics   Node: 388c457735b8

Provenance: formalization of a published result. Source: arXiv:2610.34372, Lemma 2.1

If A is a nonempty admissible subset of {1, ..., N}, then the square of the cardinality of A plus 5 is at most 6 times N.
-/

lemma admissible_card_sq_add_five_le_sum_formula (m : ℕ) :
    6 * ∑ k ∈ Finset.range (m + 1), (k * (m - k) + 1) = m * (m ^ 2 + 5) + 6 := by
  induction' m with m ih
  · simp
  · rw [Finset.sum_range_succ]
    have hlast : (m + 1) * (m + 1 - (m + 1)) + 1 = 1 := by simp
    rw [hlast]
    have hstep : ∑ x ∈ Finset.range (m + 1), (x * (m + 1 - x) + 1) =
        (∑ x ∈ Finset.range (m + 1), (x * (m - x) + 1)) + ∑ x ∈ Finset.range (m + 1), x := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_range] at hx
      have : m + 1 - x = (m - x) + 1 := by omega
      rw [this, mul_add, mul_one]
      omega
    rw [hstep]
    rw [mul_add, mul_add, ih]
    have hsum := Finset.sum_range_id_mul_two (m + 1)
    have : m + 1 - 1 = m := by omega
    rw [this] at hsum
    have h6 : 6 * ∑ x ∈ Finset.range (m + 1), x = 3 * ((∑ x ∈ Finset.range (m + 1), x) * 2) := by ring
    rw [h6, hsum]
    ring

/-- The cardinality m of a nonempty admissible subset of {1, ..., N} satisfies m^2 + 5 <= 6N. -/
theorem admissible_card_sq_add_five_le (N : ℕ) (A : Finset ℕ)
    (hA_sub : A ⊆ Finset.Icc 1 N) (hA_nonempty : A.Nonempty) (hA_adm : IsAdmissible A) :
    (A.card : ℤ) ^ 2 + 5 ≤ 6 * N := by
  have hm : 0 < A.card := Finset.Nonempty.card_pos hA_nonempty
  have hdisj : (↑(Finset.range (A.card + 1)) : Set ℕ).PairwiseDisjoint
      (fun k => (A.powersetCard k).image (Finset.sum · id)) := by
    intro i hi j hj hij
    exact pairwiseDisjoint_k_sum_of_isAdmissible hA_adm hij
  have hcard_union : ((Finset.range (A.card + 1)).biUnion
      (fun k => (A.powersetCard k).image (Finset.sum · id))).card =
      ∑ k ∈ Finset.range (A.card + 1), ((A.powersetCard k).image (Finset.sum · id)).card :=
    Finset.card_biUnion hdisj
  have h_term_le : ∀ k ∈ Finset.range (A.card + 1),
      k * (A.card - k) + 1 ≤ ((A.powersetCard k).image (Finset.sum · id)).card := by
    intro k hk
    simp only [Finset.mem_range] at hk
    exact card_powersetCard_image_sum_ge A k (by omega)
  have hsum_le_card : ∑ k ∈ Finset.range (A.card + 1), (k * (A.card - k) + 1) ≤
      ((Finset.range (A.card + 1)).biUnion (fun k => (A.powersetCard k).image (Finset.sum · id))).card := by
    rw [hcard_union]
    exact Finset.sum_le_sum h_term_le
  have h_sub_Icc : (Finset.range (A.card + 1)).biUnion
      (fun k => (A.powersetCard k).image (Finset.sum · id)) ⊆ Finset.Icc 0 (A.card * N) := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_powersetCard] at hx
    rcases hx with ⟨k, hk, B, ⟨hB_sub, hB_card⟩, rfl⟩
    rw [Finset.mem_Icc]
    refine ⟨Nat.zero_le _, ?_⟩
    exact sum_le_card_mul_of_subset_Icc N A hA_sub B hB_sub
  have hcard_le : ((Finset.range (A.card + 1)).biUnion
      (fun k => (A.powersetCard k).image (Finset.sum · id))).card ≤ A.card * N + 1 := by
    have := Finset.card_le_card h_sub_Icc
    simp only [Nat.card_Icc, tsub_zero] at this
    exact this
  have hsum_le : ∑ k ∈ Finset.range (A.card + 1), (k * (A.card - k) + 1) ≤ A.card * N + 1 :=
    le_trans hsum_le_card hcard_le
  have hmul_le : 6 * ∑ k ∈ Finset.range (A.card + 1), (k * (A.card - k) + 1) ≤ 6 * (A.card * N + 1) :=
    Nat.mul_le_mul_left 6 hsum_le
  rw [admissible_card_sq_add_five_le_sum_formula] at hmul_le
  have : 6 * (A.card * N + 1) = A.card * (6 * N) + 6 := by ring
  have hmul_le' : A.card * (A.card ^ 2 + 5) ≤ A.card * (6 * N) := by omega
  have hle : A.card ^ 2 + 5 ≤ 6 * N := Nat.le_of_mul_le_mul_left hmul_le' hm
  have hcast : ((A.card ^ 2 + 5 : ℕ) : ℤ) ≤ ((6 * N : ℕ) : ℤ) := by exact_mod_cast hle
  push_cast at hcast
  exact hcast
