import AFTD.Prelude

/-!
# symmetric_boolean_degree_deficit_three_case_15

Topic: algebraic_complexity   Node: 56609deb4bab

Provenance: helper lemma. arXiv:2611.26446, Sec. 1.3

Either there exists a natural number $t$ such that $2 \le t$ and $15 = 4t^2 - 1$, or there exists a natural number $i$ such that $2 \le i$, $i \bmod 3 \ne 1$, and $15 = f_{2i+2}f_{2i+3} + 1$, where $f_j$ denotes the $j$-th Fibonacci number.
-/

/-- The size n = 15 belongs to the two deficit-three families (t = 2 in the first family). -/
theorem symmetric_boolean_degree_deficit_three_case_15 :
    (∃ t : ℕ, 2 ≤ t ∧ 15 = 4 * t ^ 2 - 1) ∨
    (∃ i : ℕ, 2 ≤ i ∧ i % 3 ≠ 1 ∧ 15 = Nat.fib (2 * i + 2) * Nat.fib (2 * i + 3) + 1) := by
  left
  exact ⟨2, by decide, by decide⟩
