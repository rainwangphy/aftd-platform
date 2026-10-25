import AFTD.Prelude
import AFTD.Kb.Tcs.HasFractionalScdWithDenominator
import AFTD.Kb.Tcs.IsSymmetricSaturatedChain
import AFTD.Kb.Tcs.HasFractionalSymmetricChainDecomposition

/-!
# fractional_scd_of_with_denominator

Topic: combinatorics   Node: e9413485d166

Provenance: helper lemma. arXiv:2610.24148, Section 2.7.4

If a partially ordered type with an integer rank function admits a fractional symmetric chain decomposition with denominator D, then it admits a fractional symmetric chain decomposition.
-/

/-- A fractional symmetric chain decomposition with denominator D implies a fractional symmetric chain decomposition. -/
theorem fractional_scd_of_with_denominator
    {α : Type*} [PartialOrder α] (rank : α → ℤ) (D : ℕ)
    (h : has_fractional_scd_with_denominator rank D) :
    has_fractional_symmetric_chain_decomposition rank := by
  obtain ⟨𝒞, τ, h1, h2, h3, h4⟩ := h
  exact ⟨𝒞, τ, h1, h2, h4⟩
