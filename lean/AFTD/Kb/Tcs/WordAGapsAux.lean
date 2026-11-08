import AFTD.Prelude

/-!
# word_a_gaps_aux

Topic: automata   Node: 2a3213f8ba48

Provenance: helper lemma. step towards word_unary_inserted_block_exchange_exact

Auxiliary accumulator version of the 'a'-gap profile: scanning a word left to right, accumulating the count of copies of a since the last letter different from a, emitting that count when a different letter is met and ending with the trailing count.
-/

def word_a_gaps_aux {α : Type*} [DecidableEq α] (a : α) : ℕ → List α → List ℕ
  | c, [] => [c]
  | c, x :: xs => if x = a then word_a_gaps_aux a (c + 1) xs else c :: word_a_gaps_aux a 0 xs
