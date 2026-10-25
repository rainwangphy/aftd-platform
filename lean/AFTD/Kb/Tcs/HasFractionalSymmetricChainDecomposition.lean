import AFTD.Prelude
import AFTD.Kb.Tcs.IsSymmetricSaturatedChain

/-!
# has_fractional_symmetric_chain_decomposition

Topic: combinatorics   Node: a8e10cc2626e

Provenance: formalization of a published result. Source: arXiv:2610.24148, Section 2.7

A ranked poset admits a fractional symmetric chain decomposition if there exists a finite set of symmetric saturated chains and non-negative rational weights on them such that for every element in the poset, the sum of weights of chains containing that element equals 1.
-/

open scoped Classical BigOperators in
/-- A ranked poset admits a fractional symmetric chain decomposition if there exists a finite collection of symmetric saturated chains with non-negative rational weights covering each element with total weight 1. -/
def has_fractional_symmetric_chain_decomposition
    {α : Type*} [PartialOrder α] (rank : α → ℤ) : Prop :=
  ∃ (𝒞 : Finset (Set α)) (τ : Set α → ℚ),
    (∀ C ∈ 𝒞, is_symmetric_saturated_chain rank C) ∧
    (∀ C ∈ 𝒞, 0 ≤ τ C) ∧
    (∀ x : α, ∑ C ∈ 𝒞.filter (x ∈ ·), τ C = 1)
