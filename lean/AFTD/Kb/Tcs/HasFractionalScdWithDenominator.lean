import AFTD.Prelude
import AFTD.Kb.Tcs.IsSymmetricSaturatedChain

/-!
# has_fractional_scd_with_denominator

Topic: combinatorics   Node: 371ba30f3561

Provenance: formalization of a published result. Source: arXiv:2610.24148, Section 2.7.4

A partially ordered type with an integer rank function admits a fractional symmetric chain decomposition with denominator D if there exists a finite collection 𝒞 of symmetric saturated chains and a weight function τ assigning to each chain in 𝒞 a non-negative rational number of the form k / D for some natural number k, such that for every element x of the poset, the sum of weights of chains in 𝒞 containing x equals 1.
-/

open scoped Classical BigOperators in
/-- A ranked poset admits a fractional symmetric chain decomposition with denominator D if all chain weights are of the form k / D for k ∈ ℕ. -/
def has_fractional_scd_with_denominator
    {α : Type*} [PartialOrder α] (rank : α → ℤ) (D : ℕ) : Prop :=
  ∃ (𝒞 : Finset (Set α)) (τ : Set α → ℚ),
    (∀ C ∈ 𝒞, is_symmetric_saturated_chain rank C) ∧
    (∀ C ∈ 𝒞, 0 ≤ τ C) ∧
    (∀ C ∈ 𝒞, ∃ k : ℕ, τ C = (k : ℚ) / (D : ℚ)) ∧
    (∀ x : α, ∑ C ∈ 𝒞.filter (x ∈ ·), τ C = 1)
