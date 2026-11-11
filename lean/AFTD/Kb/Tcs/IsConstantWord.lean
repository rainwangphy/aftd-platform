import AFTD.Prelude

/-!
# is_constant_word

Topic: information   Node: 394af0308db8

Provenance: original. Related work: folklore

A word y on the finite index set Fin n is constant if all its symbols are equal, that is, y i = y j for all i and j in Fin n.
-/

/-- A word on Fin n is constant if all its symbols are equal. -/
def is_constant_word {n : ℕ} {α : Type*} (y : Fin n → α) : Prop := ∀ i j : Fin n, y i = y j
