import AFTD.Prelude

/-!
# word_absorb_run

Topic: information   Node: 11269c5f8c74

Provenance: original. Related work: folklore

The word obtained from y : Fin n → α by changing every letter in the index interval [a', b') to c, leaving all letters outside the interval unchanged.
-/

/-- Replace all letters of word y in the interval [a', b') by the letter c. -/
def word_absorb_run {n : ℕ} {α : Type*} (y : Fin n → α) (a' b' : ℕ) (c : α) : Fin n → α := fun i => if a' ≤ i.val ∧ i.val < b' then c else y i
