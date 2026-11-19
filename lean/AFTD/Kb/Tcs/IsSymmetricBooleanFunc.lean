import AFTD.Prelude
import AFTD.Kb.Tcs.HammingWeight

/-!
# is_symmetric_boolean_func

Topic: circuits   Node: 2ad81c932f5b

Provenance: formalization of a published result. Source: scout/2611-21910-new-gate-weight-and-wire-complexity-bounds-for-sigmoid-neur.md:889

A Boolean function f on n variables is symmetric if its value on any input depends only on the Hamming weight of the input.
-/

/-- Predicate asserting that a Boolean function f on {0,1}^n depends only on the Hamming weight of its input. -/
def is_symmetric_boolean_func {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := ∃ F : ℕ → Bool, ∀ x : Fin n → Bool, f x = F (hamming_weight x)
