import AFTD.Prelude
import AFTD.Kb.Tcs.IsQuadraticPureStateInvariant
import AFTD.Kb.Tcs.QuadraticPureStateForm
import AFTD.Kb.Tcs.PureStateInvariantAddition
import AFTD.Kb.Tcs.PureStateInvariantScaling
import AFTD.Kb.Tcs.IsPureState

/-!
# quadratic_pure_state_invariant_submodule

Topic: quantum   Node: 0025223fd0eb

Provenance: formalization of a published result. Source: arXiv:2610.36076 Sec. 3.1

The real submodule of weight vectors zeta : Fin (d^2 - 1) → ℝ that are quadratic pure-state invariants for an operator basis T.
-/

/-- The real submodule of quadratic pure-state invariant weight vectors. -/
def quadratic_pure_state_invariant_submodule {d : ℕ}
    (T : Fin (d^2 - 1) → Matrix (Fin d) (Fin d) ℂ) :
    Submodule ℝ (Fin (d^2 - 1) → ℝ) := {
  carrier := {ζ | is_quadratic_pure_state_invariant T ζ}
  zero_mem' := ⟨0, fun ρ _ => by simp [quadratic_pure_state_form]⟩
  add_mem' := fun ha hb => pure_state_invariant_addition T _ _ ha hb
  smul_mem' := fun c x hx => pure_state_invariant_scaling T x hx c
}
