import AFTD.Prelude
import AFTD.Kb.Tcs.KrawtchoukGeneratingFunction
import AFTD.Kb.Tcs.Krawtchouk

/-!
# krawtchouk_sum_eval

Topic: information   Node: 8d17f883df83

Provenance: formalization of a published result. Source: MacWilliams & Sloane, The Theory of Error-Correcting Codes (1977), Ch. 5

Total sum of Krawtchouk polynomials. Let n and x be natural numbers with x <= n. Then the sum of the binary Krawtchouk polynomials sum_{j=0}^n K_j^{(n)}(x) equals 2^n if x = 0, and equals 0 if x > 0.
-/

/-- Sum of all binary Krawtchouk polynomials: evaluates to 2^n when x = 0 and to 0 when x > 0. -/
theorem krawtchouk_sum_eval (n x : ℕ) (hx : x ≤ n) :
    ∑ j ∈ Finset.range (n + 1), krawtchouk n j x = if x = 0 then (2 : ℝ) ^ n else 0 := by
  have h := krawtchouk_generating_function n x hx 1
  simp only [one_pow, mul_one, sub_self] at h
  rw [h]
  split_ifs with hx0
  · subst hx0
    norm_num
  · rw [zero_pow hx0, zero_mul]
