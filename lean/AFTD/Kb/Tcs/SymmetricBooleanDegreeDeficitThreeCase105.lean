import AFTD.Prelude

/-!
# symmetric_boolean_degree_deficit_three_case_105

Topic: algebraic_complexity   Node: 5dd77bc29c21

Provenance: helper lemma. arXiv:2611.26446, Sec. 1.3

Either there exists a natural number $t$ such that $2 \le t$ and $105 = 4t^2 - 1$, or there exists a natural number $i$ such that $2 \le i$, $i \bmod 3 \ne 1$, and $105 = f_{2i+2}f_{2i+3} + 1$, where $f_j$ denotes the $j$-th Fibonacci number.
-/

/-- The size n = 105 belongs to the second deficit-three family (i = 2, f_6 * f_7 + 1 = 8 * 13 + 1 = 105). -/
theorem symmetric_boolean_degree_deficit_three_case_105 :
    (∃ t : ℕ, 2 ≤ t ∧ 105 = 4 * t ^ 2 - 1) ∨
    (∃ i : ℕ, 2 ≤ i ∧ i % 3 ≠ 1 ∧ 105 = Nat.fib (2 * i + 2) * Nat.fib (2 * i + 3) + 1) := by
  right
  use 2
  decide
