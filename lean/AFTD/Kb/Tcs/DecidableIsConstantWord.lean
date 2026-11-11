import AFTD.Prelude
import AFTD.Kb.Tcs.IsConstantWord

/-!
# decidable_is_constant_word

Topic: information   Node: f3973edda2a7

Provenance: original. Related work: folklore

Decidability instance for the predicate that a word on Fin n over a type with decidable equality is constant.
-/

/-- Decidability of the constant word predicate on a finite alphabet with decidable equality. -/
instance decidable_is_constant_word {n : ℕ} {α : Type*} [DecidableEq α] (y : Fin n → α) : Decidable (is_constant_word y) := Fintype.decidableForallFintype
