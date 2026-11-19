import AFTD.Prelude
import AFTD.Kb.Tcs.Depth3SigmoidCircuit
import AFTD.Kb.Tcs.Depth3SigmoidCircuitEval

/-!
# depth3_sigmoid_circuit_eval_bool

Topic: circuits   Node: 2b57ef9e946d

Provenance: formalization of a published result. Source: scout/2611-21910-new-gate-weight-and-wire-complexity-bounds-for-sigmoid-neur.md:717

Evaluates a depth-3 sigmoidal circuit C on a Boolean input vector x : Fin n → Bool by converting false to 0 and true to 1 and evaluating C.
-/

/-- Evaluation of a depth-3 sigmoidal circuit on a Boolean input assignment. -/
noncomputable def depth3_sigmoid_circuit_eval_bool {n : ℕ} (C : Depth3SigmoidCircuit n) (x : Fin n → Bool) : ℝ :=
  depth3_sigmoid_circuit_eval C (fun i => if x i then 1 else 0)
