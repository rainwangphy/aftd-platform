import AFTD.Prelude
import AFTD.Kb.Tcs.HasFractionalScdWithDenominator
import AFTD.Kb.Tcs.IsSymmetricSaturatedChain
import AFTD.Kb.Tcs.HasSymmetricChainDecomposition

/-!
# fractional_scd_with_denominator_one_of_scd

Topic: combinatorics   Node: 75d597689414

Provenance: helper lemma. arXiv:2610.24148, Section 2.7.4

If a finite partially ordered type with an integer rank function admits an ordinary symmetric chain decomposition, then it admits a fractional symmetric chain decomposition with denominator 1.
-/

open scoped Classical BigOperators in
/-- An ordinary symmetric chain decomposition yields a fractional symmetric chain decomposition with denominator 1. -/
theorem fractional_scd_with_denominator_one_of_scd
    {α : Type*} [Fintype α] [PartialOrder α] (rank : α → ℤ)
    (h : has_symmetric_chain_decomposition rank) :
    has_fractional_scd_with_denominator rank 1 := by
  classical
  obtain ⟨𝒞, hsC, huniq⟩ := h
  let s := 𝒞.toFinset
  have h1 : ∀ C ∈ s, is_symmetric_saturated_chain rank C := by
    intro C hC
    rw [Set.mem_toFinset] at hC
    exact hsC C hC
  refine ⟨s, fun _ => 1, h1, ?_, ?_, ?_⟩
  · intro C hC; norm_num
  · intro C hC; exact ⟨1, by norm_num⟩
  · intro x
    obtain ⟨C0, hC0mem, hC0uniq⟩ := huniq x
    have hfilt : s.filter (fun C => x ∈ C) = {C0} := by
      ext C
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hCs, hxC⟩
        rw [Set.mem_toFinset] at hCs
        exact hC0uniq C ⟨hCs, hxC⟩
      · intro h
        subst h
        exact ⟨by rw [Set.mem_toFinset]; exact hC0mem.1, hC0mem.2⟩
    rw [hfilt, Finset.sum_singleton]
