import AFTD.Prelude
import AFTD.Kb.Tcs.ConsecutiveSumMaxTerms

/-!
# extremal_consecutive_sum

Topic: combinatorics   Node: b156416107b9

Provenance: formalization of a published result. Source: arXiv:2611.30462 Section 3

For integers a and K, the extremal value f(a, K) defined as the integer supremum (sSup) of the set consecutive_sum_max_terms a K of terminal values of valid sequences with step bound K and distinct consecutive sums.
-/

/-- The extremal function f(a, K) defined as the supremum of terminal values of valid sequences with distinct consecutive sums. -/
noncomputable def extremal_consecutive_sum (a K : ℤ) : ℤ := sSup (consecutive_sum_max_terms a K)
