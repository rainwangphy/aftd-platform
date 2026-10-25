import AFTD.Prelude
import AFTD.Kb.Tcs.HasSymmetricChainDecomposition
import AFTD.Kb.Tcs.HasFractionalSymmetricChainDecomposition
import AFTD.Kb.Tcs.IsSymmetricSaturatedChain

/-!
# fractional_scd_of_scd

Topic: combinatorics   Node: 45d63c117494

Provenance: helper lemma. arXiv:2610.24148, Section 2.7.1

If a finite ranked poset admits an ordinary symmetric chain decomposition, then it admits a fractional symmetric chain decomposition.
-/

open scoped Classical in
/-- Every finite ranked poset admitting a symmetric chain decomposition also admits a fractional symmetric chain decomposition. -/
theorem fractional_scd_of_scd
    {α : Type*} [Fintype α] [PartialOrder α] (rank : α → ℤ)
    (h : has_symmetric_chain_decomposition rank) :
    has_fractional_symmetric_chain_decomposition rank := by
  rcases h with ⟨𝒞, hchain, hpart⟩
  refine ⟨𝒞.toFinset, fun _ => 1, ?_, ?_, ?_⟩
  · intro C hC
    rw [Set.mem_toFinset] at hC
    exact hchain C hC
  · intro C _
    exact zero_le_one
  · intro x
    rcases hpart x with ⟨C, ⟨hC𝒞, hxC⟩, huniq⟩
    have hfilt : 𝒞.toFinset.filter (x ∈ ·) = {C} := by
      ext D
      simp only [Finset.mem_filter, Set.mem_toFinset, Finset.mem_singleton]
      constructor
      · rintro ⟨hD𝒞, hxD⟩
        exact huniq D ⟨hD𝒞, hxD⟩
      · rintro rfl
        exact ⟨hC𝒞, hxC⟩
    rw [hfilt]
    simp
