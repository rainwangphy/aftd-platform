import AFTD.Prelude
import AFTD.Kb.Tcs.IsSymmetricSaturatedChain

/-!
# has_symmetric_chain_decomposition

Topic: combinatorics   Node: 31c85f93161d

Provenance: formalization of a published result. Source: arXiv:2610.24148, Section 2.3

A ranked poset admits a symmetric chain decomposition if its elements can be partitioned into symmetric saturated chains.
-/

/-- A symmetric chain decomposition of a ranked poset. -/
def has_symmetric_chain_decomposition {α : Type*} [PartialOrder α] (rank : α → ℤ) : Prop :=
  ∃ 𝒞 : Set (Set α),
    (∀ C ∈ 𝒞, is_symmetric_saturated_chain rank C) ∧
    (∀ x : α, ∃! C ∈ 𝒞, x ∈ C)
