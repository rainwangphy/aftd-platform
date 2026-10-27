import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanDerivative
import AFTD.Kb.Tcs.HasNonzeroPeriod

/-!
# boolean_derivative_dim_eight_has_period

Topic: cryptography   Node: b41d02644d74

Provenance: helper lemma. arXiv:2610.32239, Section 2

For every Boolean function g on (Fin 8 → ZMod 2) and every nonzero vector v, the directional derivative of g along v has a nonzero period.
-/

/-- The directional derivative of a Boolean function along a nonzero vector has a nonzero period. -/
theorem boolean_derivative_dim_eight_has_period (g : (Fin 8 → ZMod 2) → ZMod 2) (v : Fin 8 → ZMod 2) (hv : v ≠ 0) : has_nonzero_period (boolean_derivative v g) := by
  use v, hv
  intro x
  dsimp [boolean_derivative]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, add_comm]
