import AFTD.Prelude

/-!
# HeapCode

Topic: combinatorics   Node: 938777510a9f

Provenance: formalization of a published result. Source: arXiv:2611.05397 Section 2.3

The mixed-radix factorial-base code space for permutations of order n, consisting of tuples d where d_i ranges from 0 to i + 1 for each i from 0 to n - 2.
-/

/-- The factorial-base code space for permutations of order n. -/
def HeapCode (n : ℕ) : Type := (i : Fin (n - 1)) → Fin (i.val + 2)
