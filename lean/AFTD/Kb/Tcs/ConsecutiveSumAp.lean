import AFTD.Prelude

/-!
# consecutive_sum_ap

Topic: combinatorics   Node: 2710b12922f4

Provenance: formalization of a published result. Source: arXiv:2611.30462 Theorem 3.2

For integers a and K and a natural number i, the integer a + ((i : ℤ) - 1) * K, representing the i-th term of an arithmetic progression with first term a at index 1 and common difference K.
-/

/-- The arithmetic progression a_i = a + (i - 1) * K with start a and step K. -/
def consecutive_sum_ap (a K : ℤ) (i : ℕ) : ℤ := a + ((i : ℤ) - 1) * K
