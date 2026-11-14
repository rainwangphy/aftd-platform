import AFTD.Prelude

/-!
# multiset_max

Topic: combinatorics   Node: 4642bd4326f9

Provenance: formalization of a published result. Source: scout/2611-15780-multiple-choice-knapsack-with-small-items.md:204

The maximum element of a multiset of natural numbers s, defined as 0 if s is empty.
-/

/-- The maximum element of a multiset of natural numbers, or 0 if empty. -/
def multiset_max (s : Multiset ℕ) : ℕ := s.toFinset.sup id
