import AFTD.Prelude
import AFTD.Kb.Tcs.KrawtchoukGeneratingFunction
import AFTD.Kb.Tcs.Krawtchouk

/-!
# krawtchouk_alternating_sum_eval

Topic: information   Node: a914394f3116

Provenance: formalization of a published result. Source: MacWilliams & Sloane, The Theory of Error-Correcting Codes (1977), Ch. 5

Alternating sum of Krawtchouk polynomials. Let n and x be natural numbers with x <= n. Then the alternating sum sum_{j=0}^n (-1)^j K_j^{(n)}(x) equals 2^n if x = n, and equals 0 if x < n.
-/

/-- Alternating sum of binary Krawtchouk polynomials: evaluates to 2^n when x = n and to 0 when x < n. -/
theorem krawtchouk_alternating_sum_eval (n x : ℕ) (hx : x ≤ n) :
    ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * krawtchouk n j x = if x = n then (2 : ℝ) ^ n else 0 := by
  have hgen := krawtchouk_generating_function n x hx (-1 : ℝ)
  have h_comm : (∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * krawtchouk n j x) =
                ∑ j ∈ Finset.range (n + 1), krawtchouk n j x * (-1 : ℝ) ^ j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h_comm, hgen]
  have h1 : (1 - (-1 : ℝ)) = 2 := by ring
  have h2 : (1 + (-1 : ℝ)) = 0 := by ring
  rw [h1, h2]
  split_ifs with h
  · subst h
    rw [Nat.sub_self, pow_zero, mul_one]
  · have hpos : 0 < n - x := Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne hx h)
    rw [zero_pow (by omega), mul_zero]
