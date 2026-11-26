import AFTD.Prelude

/-!
# op1957_positive_deficit_degree_arithmetic

Topic: graphs   Node: 04215b24fd5a

Provenance: helper lemma. OP-1957; scalar matching-deficiency model, experiment 40090.

The degree, separator and odd-component count budgets imply the strengthened common-nonneighbor restriction.
-/

theorem op1957_positive_deficit_degree_arithmetic
    (k t r s q n : ℕ) (ht : r+1 ≤ t)
    (hsep : t ≤ s+1) (hodd : t+1+s ≤ q) (halpha : q ≤ k)
    (hcard : n+s+1 = 2*k+t)
    (hlarge : s+2 ≤ t+r → 3*q ≤ n) :
    2*t+r ≤ k := by
  by_cases h : s+2 ≤ t+r
  · have hthree := hlarge h
    omega
  · omega
