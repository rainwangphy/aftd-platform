import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWordXor
import AFTD.Kb.Tcs.BrgcWordLowOnes
import AFTD.Kb.Tcs.BrgcWordInjective
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_word_one_bit_iff_rank_reflection

Topic: combinatorics   Node: d020789b5ca4

Provenance: helper lemma. Supporting arithmetic and canonical-representative lemmas for OP-392, arXiv:2610.24758, Conjecture 1.

Two Gray words differ exactly in bit k if and only if their ranks differ by exclusive-or with k+1 low one-bits.
-/

theorem brgc_word_one_bit_iff_rank_reflection (t u k : ℕ) :
    brgc_word t ^^^ brgc_word u = 2 ^ k ↔
      t ^^^ u = 2 ^ (k + 1) - 1 := by
  constructor
  · intro h
    apply brgc_word_injective
    rw [brgc_word_xor, h, brgc_word_low_ones]
  · intro h
    rw [← brgc_word_xor, h, brgc_word_low_ones]
