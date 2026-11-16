import AFTD.Prelude

/-!
# triangular_number

Topic: combinatorics   Node: e39c40b4d12a

Provenance: formalization of a published result. Source: arXiv:2611.17360 line 120

For any natural number k, the k-th triangular number is defined as k(k+1)/2.
-/

/-- The k-th triangular number k(k+1)/2. -/
def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2
