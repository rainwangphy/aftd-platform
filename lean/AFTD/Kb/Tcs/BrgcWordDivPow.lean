import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_word_div_pow

Topic: combinatorics   Node: 63941e68f551

Provenance: helper lemma. Prefix-parity inverse and supporting arithmetic for OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

Taking a high-bit prefix commutes with binary reflected Gray encoding.
-/

theorem brgc_word_div_pow (t k : ℕ) :
    brgc_word t / 2 ^ k = brgc_word (t / 2 ^ k) := by
  simp only [brgc_word, Nat.xor_div_two_pow, Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm 2 (2 ^ k)]
