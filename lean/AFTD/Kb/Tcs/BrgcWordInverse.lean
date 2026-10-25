import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BrgcWordXor

/-!
# brgc_word_inverse

Topic: combinatorics   Node: 5d9a87429bab

Provenance: helper lemma. Prefix-parity inverse and supporting arithmetic for OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

Encoding the n-bit inverse prefix-parity transform recovers the word.
-/

theorem brgc_word_inverse {n x : ℕ} (hx : x < 2 ^ n) :
    brgc_word (brgc_inverse n x) = x := by
  induction n generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    simp [this, brgc_inverse, brgc_word]
  | succ n ih =>
    have hhalf : x / 2 < 2 ^ n := by
      rw [pow_succ] at hx
      omega
    rw [brgc_inverse, brgc_word_xor, ih hhalf]
    simp only [brgc_word]
    simp [Nat.xor_assoc]
