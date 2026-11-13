import AFTD.Prelude

/-!
# mod5_rational_quadratic_blue_witness

Topic: combinatorics   Node: b55568f3ef85

Provenance: helper lemma. Exact rational witness from experiment 25409 for OP-1482.

For each integer k from 0 through 16, the floor of (149/100) k² + (183/50) k + 5569/1490 is nonzero modulo 5.
-/

theorem mod5_rational_quadratic_blue_witness (k : Fin 17) : (⌊(149 / 100 : ℝ) * (k.val : ℝ)^2 + (183 / 50 : ℝ) * k.val + 5569 / 1490⌋ : ℤ) % 5 ≠ 0 := by
  set_option maxRecDepth 4096 in
    set_option maxHeartbeats 2000000 in
      fin_cases k <;> norm_num
