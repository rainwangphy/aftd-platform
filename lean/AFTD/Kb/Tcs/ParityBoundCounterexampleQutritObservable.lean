import AFTD.Prelude

/-!
# parity_bound_counterexample_qutrit_observable

Topic: quantum   Node: cf1c6b1ba76b

Provenance: helper lemma. step towards open_problem_735_parity_bound_higher_dimension

The qutrit end-node observable family of the counterexample to the higher-dimensional parity bound: at setting y = 0 it is diag(1, -1, 1) acting on the middle basis vector, at setting y = 1 it is the 3x3 identity.
-/

/-- Qutrit (d = 3) end-node observable family of the parity-bound counterexample; diag(1,-1,1) at setting 0, identity at setting 1. -/
def parity_bound_counterexample_qutrit_observable : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ := fun y => if y = 0 then Matrix.diagonal (fun i : Fin 3 => if i = 1 then (-1 : ℂ) else 1) else 1
