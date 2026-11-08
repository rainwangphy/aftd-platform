import AFTD.Prelude
import AFTD.Kb.Tcs.SumsetRepCount
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.SumsetFinsetSortedVector
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.SumsetSumVectorsFinset

/-!
# sumset_rep_count_eq_zero_of_gt

Topic: combinatorics   Node: f6f8ee392c64

Provenance: formalization of a published result. Source: arXiv:2611.07303 Proposition 5.7

For any k ≥ 1, h, q, and integer s > (h + 1) * q, the representation count ν_q(s) is zero.
-/

lemma sumset_rep_count_eq_zero_of_gt_sorted (k : ℕ) (A : Finset ℤ) (hA : A.card = k) :
    sumset_finset_sorted_vector k A = ⇑(A.orderEmbOfFin hA) :=
  dif_pos hA

lemma sumset_rep_count_eq_zero_of_gt_mem_vectors (h k : ℕ) (x : Fin k → ℤ) :
    x ∈ sumset_sum_vectors_finset h k ↔ (∀ i : Fin k, 0 ≤ x i ∧ x i ≤ (h : ℤ)) ∧ ∑ i, x i = (h : ℤ) := by
  unfold sumset_sum_vectors_finset
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  apply and_congr_left
  intro _
  constructor
  · intro h1 i
    have hi := h1 i
    rw [Finset.mem_image] at hi
    obtain ⟨n, hn, heq⟩ := hi
    rw [Finset.mem_range] at hn
    rw [← heq]
    omega
  · intro h1 i
    rw [Finset.mem_image]
    refine ⟨(x i).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      have := (h1 i).1
      have := (h1 i).2
      omega
    · have := (h1 i).1
      omega

/-- The representation count ν_q(s) vanishes for s > (h + 1) * q. -/
theorem sumset_rep_count_eq_zero_of_gt (k h q : ℕ) (hk : 1 ≤ k) (s : ℤ)
    (hs : ((h : ℤ) + 1) * (q : ℤ) < s) :
    sumset_rep_count h k q s = 0 := by
  unfold sumset_rep_count
  rw [Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  rintro ⟨x, A⟩ hp
  simp only
  intro heq
  rw [Finset.mem_product] at hp
  obtain ⟨hxb, hAb⟩ := hp
  rw [sumset_rep_count_eq_zero_of_gt_mem_vectors] at hxb
  obtain ⟨hx0, hxsum⟩ := hxb
  rw [Finset.mem_powersetCard] at hAb
  obtain ⟨hAS, hAcard⟩ := hAb
  have hbound : ∀ i : Fin k, A.orderEmbOfFin hAcard i ≤ (q : ℤ) := by
    intro i
    have hh := hAS (Finset.orderEmbOfFin_mem A hAcard i)
    rw [Finset.mem_Icc] at hh
    exact hh.2
  have hdot : dotProduct x (sumset_finset_sorted_vector k A)
      = ∑ i : Fin k, x i * A.orderEmbOfFin hAcard i := by
    rw [sumset_rep_count_eq_zero_of_gt_sorted k A hAcard]
    simp only [dotProduct]
  have hle : dotProduct x (sumset_finset_sorted_vector k A) ≤ ((h : ℤ) + 1) * (q : ℤ) := by
    rw [hdot]
    have h1 : ∑ i : Fin k, x i * (q : ℤ) = ((h : ℤ) + 1) * (q : ℤ) := by
      rw [← Finset.sum_mul, hxsum]; push_cast; ring
    rw [← h1]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hbound i) (hx0 i).1
  omega
