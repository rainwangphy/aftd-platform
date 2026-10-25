import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWordXor
import AFTD.Kb.Tcs.BrgcWordLowOnes
import AFTD.Kb.Tcs.BitwordNecklaceAdjacent
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.BrgcWord

/-!
# bitword_necklace_adjacent_of_brgc_rank_reflection

Topic: combinatorics   Node: d599581854ee

Provenance: helper lemma. Supporting arithmetic and canonical-representative lemmas for OP-392, arXiv:2610.24758, Conjecture 1.

If two Gray ranks differ by exclusive-or with k+1 low one-bits and k is less than the word length, their words are adjacent with rotation zero.
-/

theorem bitword_necklace_adjacent_of_brgc_rank_reflection (n t u k : ℕ)
    (hk : k < n) (h : t ^^^ u = 2 ^ (k + 1) - 1) :
    bitword_necklace_adjacent n (brgc_word t) (brgc_word u) := by
  refine ⟨0, by omega, k, hk, ?_⟩
  simp only [Function.iterate_zero, id_eq]
  rw [← brgc_word_xor, h, brgc_word_low_ones]
