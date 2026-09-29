import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanCircuit
import AFTD.Kb.Tcs.BooleanCircuitEval

/-!
# boolean_circuit_eval_demorgan_and

Topic: circuits   Node: 3d162c809b36

For any Boolean circuits c₁ and c₂ on n variables and any input assignment x : Fin n → Bool, evaluating the negation of their conjunction BooleanCircuit.not (BooleanCircuit.and c₁ c₂) on x equals evaluating the disjunction of their negations BooleanCircuit.or (BooleanCircuit.not c₁) (BooleanCircuit.not c₂) on x.
-/

/-- De Morgan's law for circuit evaluation: the negation of an AND circuit equals the OR of the negated circuits. -/
theorem boolean_circuit_eval_demorgan_and {n : Nat} (c₁ c₂ : BooleanCircuit n) (x : Fin n → Bool) : boolean_circuit_eval (BooleanCircuit.not (BooleanCircuit.and c₁ c₂)) x = boolean_circuit_eval (BooleanCircuit.or (BooleanCircuit.not c₁) (BooleanCircuit.not c₂)) x := by
  simp [boolean_circuit_eval]
