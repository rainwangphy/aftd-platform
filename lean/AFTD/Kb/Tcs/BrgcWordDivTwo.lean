import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_word_div_two

Topic: combinatorics   Node: 5c7d73ddab0b

Provenance: helper lemma. Supporting arithmetic and canonical-representative lemmas for OP-392, arXiv:2610.24758, Conjecture 1.

The binary reflected Gray encoding commutes with division by two.
-/

theorem brgc_word_div_two (t : ℕ) :
    brgc_word t / 2 = brgc_word (t / 2) := by
  exact Nat.xor_div_two
