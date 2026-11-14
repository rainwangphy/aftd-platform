import AFTD.Prelude

/-!
# multiset_positive_subset_sums

Topic: combinatorics   Node: bb81debd7d51

Provenance: formalization of a published result. Source: scout/2611-15780-multiple-choice-knapsack-with-small-items.md:207

The finite set (of type Finset ℕ) of all sums of nonempty submultisets of a multiset s of natural numbers.
-/

/-- The finite set S*(s) of sums of nonempty submultisets of a multiset s. -/
def multiset_positive_subset_sums (s : Multiset ℕ) : Finset ℕ := ((s.powerset.filter (· ≠ 0)).map Multiset.sum).toFinset
