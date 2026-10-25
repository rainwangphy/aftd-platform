import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_word_xor

Topic: combinatorics   Node: 2ffb520463b8

Provenance: helper lemma. Supporting arithmetic and canonical-representative lemmas for OP-392, arXiv:2610.24758, Conjecture 1.

Binary reflected Gray encoding preserves bitwise exclusive-or.
-/

theorem brgc_word_xor (t u : ℕ) :
    brgc_word (t ^^^ u) = brgc_word t ^^^ brgc_word u := by
  simp only [brgc_word, Nat.xor_div_two]
  ac_rfl
