import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_word_two

Topic: combinatorics   Node: d198be419a89

Provenance: helper lemma. sanity check for brgc_word (OP-392)

Sanity check: the BRGC word of rank 2 is 011.
-/

theorem brgc_word_two : brgc_word 2 = 3 := by decide
