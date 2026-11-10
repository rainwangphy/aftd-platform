import AFTD.Prelude

/-!
# is_complete_sequence

Topic: elementary_number_theory   Node: 31c746c282d5

Provenance: formalization of a published result. Source: arXiv:2611.10200, Section 1 and Appendix A

A sequence of integers H : ℕ → ℤ is complete if every positive integer t ≥ 1 can be expressed as a sum of terms ∑_{i ∈ S} H i over a finite set of positive indices S ⊆ {i : ℕ | 1 ≤ i}.
-/

/-- A sequence of integers is complete if every positive integer is a sum of distinct positive-indexed terms. -/
def is_complete_sequence (H : ℕ → ℤ) : Prop :=
  ∀ t : ℤ, 1 ≤ t → ∃ S : Finset ℕ, (∀ i ∈ S, 1 ≤ i) ∧ ∑ i ∈ S, H i = t
