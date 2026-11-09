import AFTD.Prelude

/-!
# word_subtraction_buffer

Topic: combinatorial_games   Node: 0170f920f06e

Provenance: helper lemma. step towards word_subtraction_is_regular

The buffer of a word w in a window of width n: the i-th letter of w from the right, or none if w has at most i letters.
-/

/-- Reverse window of width n as an Option-valued Fin n vector. -/
def word_subtraction_buffer {α : Type*} (n : ℕ) (w : List α) : Fin n → Option α := fun i => w.reverse[(i : ℕ)]?
