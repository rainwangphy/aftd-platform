import AFTD.Prelude
import AFTD.Kb.Tcs.WordAGapsMaskAux

/-!
# word_a_gaps_mask

Topic: automata   Node: ec043d1128f6

Provenance: helper lemma. step towards word_unary_inserted_block_exchange_exact

The masked 'a'-gap profile of w under mask M: for each gap of w, the pair (number of false-labelled copies of a in it, number of true-labelled copies of a in it).
-/

def word_a_gaps_mask {α : Type*} [DecidableEq α] (a : α) (w : List α) (M : List Bool) : List (ℕ × ℕ) := word_a_gaps_mask_aux a 0 0 (w.zip M)
