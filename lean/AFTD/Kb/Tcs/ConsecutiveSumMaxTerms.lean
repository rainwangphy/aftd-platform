import AFTD.Prelude
import AFTD.Kb.Tcs.IsValidConsecutiveSumSeq

/-!
# consecutive_sum_max_terms

Topic: combinatorics   Node: c8d3e3352fa0

Provenance: formalization of a published result. Source: arXiv:2611.30462 Section 3

For integers a and K, the set of all integers x such that there exist a length n : ℕ and a sequence s : ℕ → ℤ satisfying is_valid_consecutive_sum_seq a K n s and s n = x, collecting the terminal values across all valid sequences of any length.
-/

/-- The set of terminal values s(n) of valid sequences starting at a with step bound K and distinct consecutive sums. -/
def consecutive_sum_max_terms (a K : ℤ) : Set ℤ :=
  { x : ℤ | ∃ (n : ℕ) (s : ℕ → ℤ), is_valid_consecutive_sum_seq a K n s ∧ s n = x }
