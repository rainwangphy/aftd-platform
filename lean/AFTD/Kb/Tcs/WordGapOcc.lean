import AFTD.Prelude
import AFTD.Kb.Tcs.WordAGaps
import AFTD.Kb.Tcs.WordOccp

/-!
# word_gap_occ

Topic: automata   Node: f54e437f01c5

Provenance: helper lemma. step towards word_unary_inserted_block_exchange_exact

The number of gaps in which w has strictly more copies of a than v: the number of indices at which the 'a'-gap profile of w exceeds that of v.
-/

def word_gap_occ {α : Type*} [DecidableEq α] (a : α) (v w : List α) : ℕ := word_occp (word_a_gaps a w) (word_a_gaps a v)
