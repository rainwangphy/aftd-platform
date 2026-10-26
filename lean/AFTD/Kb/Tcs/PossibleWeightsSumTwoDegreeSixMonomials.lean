import AFTD.Prelude
import AFTD.Kb.Tcs.HammingNormSumTwoDegreeSixMonomials
import AFTD.Kb.Tcs.Monomial

/-!
# possible_weights_sum_two_degree_six_monomials

Topic: information   Node: 77f7d0f86aea

Provenance: formalization of a published result. Source: arXiv:2610.29807, Lemma 3.2: Some Results on the Weight Spectrum of Binary Reed-Muller Codes RM(m-7,m)

The set of Hamming norms of all sums monomial I + monomial J of two coordinate monomials corresponding to 6-element subsets I, J of Fin 12 on (Fin 12 → ZMod 2) to ZMod 2 is {0, 64, 96, 112, 120, 124, 126}.
-/

/-- The set of possible Hamming weights of sums of two degree-6 coordinate monomials in 12 variables is {0, 64, 96, 112, 120, 124, 126}. -/
theorem possible_weights_sum_two_degree_six_monomials :
    {w : ℕ | ∃ (I J : Finset (Fin 12)), I.card = 6 ∧ J.card = 6 ∧
      hammingNorm (monomial I + monomial J) = w} =
    {0, 64, 96, 112, 120, 124, 126} := by
  let I : Finset (Fin 12) := {0, 1, 2, 3, 4, 5}
  ext w
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨I', J', hI, hJ, rfl⟩
    rw [hamming_norm_sum_two_degree_six_monomials I' J' hI hJ]
    have h_le : (I' ∩ J').card ≤ 6 := by
      have := @Finset.card_le_card _ (I' ∩ J') I' Finset.inter_subset_left
      omega
    interval_cases (I' ∩ J').card <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · refine ⟨I, {0, 1, 2, 3, 4, 5}, by decide, by decide, ?_⟩
      rw [hamming_norm_sum_two_degree_six_monomials I {0, 1, 2, 3, 4, 5} (by decide) (by decide)]
      have : (I ∩ {0, 1, 2, 3, 4, 5}).card = 6 := by decide
      rw [this]; rfl
    · refine ⟨I, {0, 1, 2, 3, 4, 6}, by decide, by decide, ?_⟩
      rw [hamming_norm_sum_two_degree_six_monomials I {0, 1, 2, 3, 4, 6} (by decide) (by decide)]
      have : (I ∩ {0, 1, 2, 3, 4, 6}).card = 5 := by decide
      rw [this]; rfl
    · refine ⟨I, {0, 1, 2, 3, 6, 7}, by decide, by decide, ?_⟩
      rw [hamming_norm_sum_two_degree_six_monomials I {0, 1, 2, 3, 6, 7} (by decide) (by decide)]
      have : (I ∩ {0, 1, 2, 3, 6, 7}).card = 4 := by decide
      rw [this]; rfl
    · refine ⟨I, {0, 1, 2, 6, 7, 8}, by decide, by decide, ?_⟩
      rw [hamming_norm_sum_two_degree_six_monomials I {0, 1, 2, 6, 7, 8} (by decide) (by decide)]
      have : (I ∩ {0, 1, 2, 6, 7, 8}).card = 3 := by decide
      rw [this]; rfl
    · refine ⟨I, {0, 1, 6, 7, 8, 9}, by decide, by decide, ?_⟩
      rw [hamming_norm_sum_two_degree_six_monomials I {0, 1, 6, 7, 8, 9} (by decide) (by decide)]
      have : (I ∩ {0, 1, 6, 7, 8, 9}).card = 2 := by decide
      rw [this]; rfl
    · refine ⟨I, {0, 6, 7, 8, 9, 10}, by decide, by decide, ?_⟩
      rw [hamming_norm_sum_two_degree_six_monomials I {0, 6, 7, 8, 9, 10} (by decide) (by decide)]
      have : (I ∩ {0, 6, 7, 8, 9, 10}).card = 1 := by decide
      rw [this]; rfl
    · refine ⟨I, {6, 7, 8, 9, 10, 11}, by decide, by decide, ?_⟩
      rw [hamming_norm_sum_two_degree_six_monomials I {6, 7, 8, 9, 10, 11} (by decide) (by decide)]
      have : (I ∩ {6, 7, 8, 9, 10, 11}).card = 0 := by decide
      rw [this]; rfl
