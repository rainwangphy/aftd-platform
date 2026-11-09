import AFTD.Prelude
import AFTD.Kb.Tcs.PairEncodeInjective

/-!
# list_reverse_append_singleton_getElem?

Topic: combinatorial_games   Node: 067f2dbe2a03

Provenance: helper lemma. step towards word_subtraction_is_regular

Appending a letter to w puts that letter at position 0 of the reversed word and shifts every other position by one.
-/

/-- Reverse of an append is a cons; read off positions 0 and j+1. -/
theorem list_reverse_append_singleton_getElem? {α : Type*} (w : List α) (c : α) :
    (w ++ [c]).reverse[0]? = some c ∧ ∀ j : ℕ, (w ++ [c]).reverse[(j+1)]? = w.reverse[j]? := by first | exact pair_encode_injective | (apply pair_encode_injective <;> assumption) | (apply pair_encode_injective <;> simp_all) | simpa using pair_encode_injective
