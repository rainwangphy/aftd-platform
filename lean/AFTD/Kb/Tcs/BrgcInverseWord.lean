import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BrgcWordInjective
import AFTD.Kb.Tcs.BrgcWordInverse

/-!
# brgc_inverse_word

Topic: combinatorics   Node: d349226e39b5

Provenance: helper lemma. Prefix-parity inverse and supporting arithmetic for OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

The n-bit inverse prefix-parity transform recovers an n-bit Gray rank from its encoded word.
-/

theorem brgc_inverse_word {n t : ℕ} (ht : t < 2 ^ n) :
    brgc_inverse n (brgc_word t) = t := by
  apply brgc_word_injective
  apply brgc_word_inverse
  exact Nat.xor_lt_two_pow ht (lt_of_le_of_lt (Nat.div_le_self _ _) ht)
