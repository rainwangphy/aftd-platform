import AFTD.Prelude

/-!
# traceBinomialGap

Topic: quantum_mechanics   Node: 60696c2595ec

Provenance: formalization of a published result. Source: arXiv:2411.33774

For d by d complex matrices A and B and a natural number k, the trace binomial gap Delta_k(A, B) is the difference between the binomial trace sum sum_{j=0}^k binom(k, j) Re tr(A^j B^(k-j)) and Re tr((A + B)^k).
-/

/-- The noncommutative trace binomial gap Delta_k(A, B) = sum_{j=0}^k binom(k,j) Re tr(A^j B^(k-j)) - Re tr((A+B)^k). -/
def traceBinomialGap {d : ℕ} (k : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (Matrix.trace (A ^ j * B ^ (k - j))).re) -
    (Matrix.trace ((A + B) ^ k)).re
