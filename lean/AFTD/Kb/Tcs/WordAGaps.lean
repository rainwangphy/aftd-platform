import AFTD.Prelude
import AFTD.Kb.Tcs.WordAGapsAux

/-!
# word_a_gaps

Topic: automata   Node: d968cd04e5c8

Provenance: helper lemma. step towards word_unary_inserted_block_exchange_exact

The 'a'-gap profile of a word: the list whose j-th entry is the number of copies of a appearing in the j-th gap, the gaps being the maximal segments delimited by the letters different from a (so the list has length (number of letters different from a) + 1).
-/

def word_a_gaps {α : Type*} [DecidableEq α] (a : α) (w : List α) : List ℕ := word_a_gaps_aux a 0 w
