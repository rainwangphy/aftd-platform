import AFTD.Prelude

/-!
# multiset_is_minimal_zero_sum

Topic: elementary_number_theory   Node: 03949f41134f

Provenance: formalization of a published result. Source: arXiv:2610.16562 (The Davenport constant of low-dimensional boxes), Sec. 1 (minimal zero-sum sequences).

A minimal zero-sum sequence: a nonempty finite sequence (multiset) with sum zero, no nonempty proper subsequence of which has sum zero.
-/

/-- A minimal zero-sum sequence. -/
def multiset_is_minimal_zero_sum {G : Type*} [AddCommMonoid G] (s : Multiset G) : Prop :=
  s ≠ 0 ∧ s.sum = 0 ∧ ∀ t ≤ s, t ≠ 0 → t.sum = 0 → t = s
