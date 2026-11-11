import AFTD.Prelude
import AFTD.Kb.Tcs.IsWordRun

/-!
# is_longest_word_run

Topic: information   Node: b4615c8c98af

Provenance: original. Related work: folklore

A run [a, b) of a word y : Fin n → α is a longest run if its length b - a is greater than or equal to the length b' - a' of every run [a', b') of y.
-/

/-- A run [a, b) of y is a longest run if its length b - a is at least the length of every run of y. -/
def is_longest_word_run {n : ℕ} {α : Type*} (y : Fin n → α) (a b : ℕ) : Prop := is_word_run y a b ∧ ∀ a' b' : ℕ, is_word_run y a' b' → b' - a' ≤ b - a
