import AFTD.Prelude

/-!
# is_symmetric_saturated_chain

Topic: combinatorics   Node: 79e47a12b557

Provenance: formalization of a published result. Source: arXiv:2610.24148, Section 2.3

A subset of a ranked poset is a symmetric saturated chain if there is an integer k such that the chain contains exactly one element of each rank -k + 2j for 0 <= j <= k, contains no elements of any other rank, and adjacent elements along the chain satisfy the cover relation.
-/

/-- A subset of a ranked poset is a symmetric saturated chain. -/
def is_symmetric_saturated_chain {α : Type*} [PartialOrder α] (rank : α → ℤ) (C : Set α) : Prop :=
  ∃ k : ℤ,
    (∀ m : ℤ, (∃ x ∈ C, rank x = m) ↔ (∃ j : ℤ, 0 ≤ j ∧ j ≤ k ∧ m = -k + 2 * j)) ∧
    (∀ x ∈ C, ∀ y ∈ C, rank x = rank y → x = y) ∧
    (∀ x ∈ C, ∀ y ∈ C, rank y = rank x + 2 → x ⋖ y)
