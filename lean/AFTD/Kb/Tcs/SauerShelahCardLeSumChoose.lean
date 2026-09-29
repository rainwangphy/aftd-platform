import AFTD.Prelude

/-!
# sauer_shelah_card_le_sum_choose

Topic: combinatorics   Node: 155f9d07c3a5

Sauer-Shelah lemma: let α be a finite set with n elements and let A be a finite family of subsets of α. If the VC-dimension of A, that is the largest size of a set s such that every subset of s occurs as s ∩ u for some u ∈ A, is at most d, then A has at most ∑_{k=0}^{d} binom(n,k) members.
-/

/-- Sauer-Shelah lemma: a set family of VC-dimension at most `d` on an `n`-element ground set has at most `∑_{k ≤ d} n.choose k` members. -/
theorem sauer_shelah_card_le_sum_choose {α : Type*} [Fintype α] [DecidableEq α] (𝒜 : Finset (Finset α)) (d : ℕ)
    (h : 𝒜.vcDim ≤ d) : 𝒜.card ≤ ∑ k ∈ Finset.Iic d, (Fintype.card α).choose k := by
  calc 𝒜.card ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card α).choose k := Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic d, (Fintype.card α).choose k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Iic_subset_Iic.2 h
        · intro k _ _
          positivity
