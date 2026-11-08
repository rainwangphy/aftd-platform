import AFTD.Prelude
import AFTD.Kb.Tcs.SumsetRepCount
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.SumsetFinsetSortedVector
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.SumsetSumVectorsFinset

/-!
# sumset_rep_count_eq_zero_of_lt

Topic: combinatorics   Node: 400b8b10bf4e

Provenance: formalization of a published result. Source: arXiv:2611.07303 Proposition 5.7

For any k ≥ 1, h, q, and integer s < h + 1, the representation count ν_q(s) is zero.
-/

private theorem sumset_rep_count_eq_zero_of_lt_aux_mem_vectors (h k : ℕ) (x : Fin k → ℤ) :
    x ∈ sumset_sum_vectors_finset h k ↔
      (∀ i, 0 ≤ x i ∧ x i ≤ (h : ℤ)) ∧ ∑ i, x i = (h : ℤ) := by
  unfold sumset_sum_vectors_finset
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, h2⟩
    have := h1 i
    simp only [Finset.mem_image, Finset.mem_range] at this
    obtain ⟨n, hn, heq⟩ := this
    rw [← heq]; constructor <;> omega
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, h2⟩
    obtain ⟨h0, hle⟩ := h1 i
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨(x i).toNat, by omega, by omega⟩

private theorem sumset_rep_count_eq_zero_of_lt_aux_sorted (k : ℕ) (A : Finset ℤ)
    (hA : A.card = k) : sumset_finset_sorted_vector k A = A.orderEmbOfFin hA := by
  unfold sumset_finset_sorted_vector
  rw [dif_pos hA]

/-- The representation count ν_q(s) vanishes for s < h + 1. -/
theorem sumset_rep_count_eq_zero_of_lt (k h q : ℕ) (hk : 1 ≤ k) (s : ℤ)
    (hs : s < (h : ℤ) + 1) :
    sumset_rep_count h k q s = 0 := by
  unfold sumset_rep_count
  rw [Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  rintro ⟨x, A⟩ hp
  simp only
  intro heq
  rw [Finset.mem_product] at hp
  obtain ⟨hxb, hAb⟩ := hp
  rw [sumset_rep_count_eq_zero_of_lt_aux_mem_vectors] at hxb
  obtain ⟨hx0, hxsum⟩ := hxb
  rw [Finset.mem_powersetCard] at hAb
  obtain ⟨hAS, hAcard⟩ := hAb
  have hbound : ∀ i : Fin k, (1 : ℤ) ≤ A.orderEmbOfFin hAcard i := by
    intro i
    have hh := hAS (Finset.orderEmbOfFin_mem A hAcard i)
    rw [Finset.mem_Icc] at hh
    exact hh.1
  have hdot : dotProduct x (sumset_finset_sorted_vector k A)
      = ∑ i : Fin k, x i * A.orderEmbOfFin hAcard i := by
    rw [sumset_rep_count_eq_zero_of_lt_aux_sorted k A hAcard]
    simp only [dotProduct]
  have hge : (h : ℤ) + 1 ≤ dotProduct x (sumset_finset_sorted_vector k A) := by
    rw [hdot]
    have h1 : ∑ i : Fin k, x i = (h : ℤ) + 1 := by
      rw [hxsum]; push_cast; ring
    rw [← h1]
    apply Finset.sum_le_sum
    intro i _
    calc x i = x i * 1 := by ring
      _ ≤ x i * A.orderEmbOfFin hAcard i :=
        mul_le_mul_of_nonneg_left (hbound i) (hx0 i).1
  omega
