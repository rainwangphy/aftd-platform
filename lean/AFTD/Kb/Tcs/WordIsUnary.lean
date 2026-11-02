import AFTD.Prelude

/-!
# word_is_unary

Topic: automata   Node: a8063cf36a04

Provenance: formalization of a published result. Source: arXiv:2610.39941 Section 5

A word over an alphabet is unary if it is a nonempty power of a single letter, that is, it is the repetition of some letter a for a positive number n of times.
-/

/-- A word is unary if it is a positive repetition of a single letter. -/
def word_is_unary {α : Type*} (s : List α) : Prop := ∃ a : α, ∃ n : ℕ, s = List.replicate n a ∧ 0 < n
