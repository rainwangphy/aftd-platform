import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanDerivative

/-!
# boolean_derivative_zero

Topic: cryptography   Node: 65c86a90f40a

Provenance: helper lemma. folklore

For any Boolean function f on (Fin n → ZMod 2), the directional derivative of f along the zero vector is the zero function.
-/

/-- The directional derivative along zero is zero. -/
theorem boolean_derivative_zero {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) : boolean_derivative 0 f = 0 := by
  ext x
  simp [boolean_derivative, CharTwo.add_self_eq_zero]
