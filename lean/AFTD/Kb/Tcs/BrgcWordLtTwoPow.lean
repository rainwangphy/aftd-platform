import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_word_lt_two_pow

Topic: combinatorics   Node: 60972a76e200

Provenance: helper lemma. Supporting arithmetic and canonical-representative lemmas for OP-392, arXiv:2610.24758, Conjecture 1.

An n-bit rank encodes an n-bit word.
-/

theorem brgc_word_lt_two_pow {n t : ℕ} (ht : t < 2 ^ n) :
    brgc_word t < 2 ^ n := by
  exact Nat.xor_lt_two_pow ht (lt_of_le_of_lt (Nat.div_le_self _ _) ht)
