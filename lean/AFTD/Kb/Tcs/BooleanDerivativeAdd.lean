import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanDerivative

/-!
# boolean_derivative_add

Topic: cryptography   Node: 1328f648537c

Provenance: helper lemma. step towards boolean_derivative_conjecture_dim_eight

The directional derivative operator D_v on Boolean functions is additive: D_v(g + h) = D_v(g) + D_v(h).
-/

/-- The directional derivative of Boolean functions is linear over ZMod 2. -/
theorem boolean_derivative_add {n : ℕ} (v : Fin n → ZMod 2) (g h : (Fin n → ZMod 2) → ZMod 2) : boolean_derivative v (g + h) = boolean_derivative v g + boolean_derivative v h := by
  ext x
  simp only [boolean_derivative, Pi.add_apply]
  ring
