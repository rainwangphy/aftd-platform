import AFTD.Prelude

/-!
# word_a_gaps_mask_aux

Topic: automata   Node: 7cce10f024b7

Provenance: helper lemma. step towards word_unary_inserted_block_exchange_exact

Auxiliary version of the masked gap profile: scanning letter/mask-label pairs, accumulating for the current gap the number of false-labelled copies of a and of true-labelled copies of a, emitting the pair when a letter different from a is met.
-/

def word_a_gaps_mask_aux {α : Type*} [DecidableEq α] (a : α) : ℕ → ℕ → List (α × Bool) → List (ℕ × ℕ)
  | f, t, [] => [(f, t)]
  | f, t, (x, b) :: xs =>
      if x = a then (if b then word_a_gaps_mask_aux a f (t + 1) xs else word_a_gaps_mask_aux a (f + 1) t xs)
      else (f, t) :: word_a_gaps_mask_aux a 0 0 xs
