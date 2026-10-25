import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcInverse

/-!
# brgc_inverse_lt_two_pow

Topic: combinatorics   Node: 6db2ef89e3c6

Provenance: helper lemma. Prefix-parity inverse and supporting arithmetic for OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

The inverse prefix-parity transform of an n-bit word has an n-bit rank.
-/

theorem brgc_inverse_lt_two_pow {n x : ℕ} (hx : x < 2 ^ n) : brgc_inverse n x < 2 ^ n := by
  induction n generalizing x with
  | zero => simp [brgc_inverse]
  | succ n ih =>
    have hhalf : x / 2 < 2 ^ n := by
      rw [pow_succ] at hx
      omega
    apply Nat.xor_lt_two_pow hx
    exact lt_of_lt_of_le (ih hhalf) (Nat.pow_le_pow_right (by decide) (by omega))
