import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanCircuit
import AFTD.Kb.Tcs.BooleanCircuitEval

/-!
# boolean_circuit_eval_not_not

Topic: circuits   Node: 3f8430c02b51

For any Boolean circuit c on n variables and any input assignment x : Fin n → Bool, evaluating the double negation BooleanCircuit.not (BooleanCircuit.not c) on x equals evaluating c on x.
-/

/-- Evaluating the double negation of a circuit yields the same value as the circuit itself. -/
theorem boolean_circuit_eval_not_not {n : Nat} (c : BooleanCircuit n) (x : Fin n → Bool) : boolean_circuit_eval (BooleanCircuit.not (BooleanCircuit.not c)) x = boolean_circuit_eval c x := by
  simp [boolean_circuit_eval]
