import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanCircuit

/-!
# boolean_circuit_eval

Topic: circuits   Node: d45f14cd72fe

Evaluates a Boolean circuit c with n inputs on a variable truth assignment x : Fin n → Bool, by structural recursion: variables look up their value in x, constants return their Boolean value, and NOT, AND, OR gates apply the corresponding Boolean operations to the evaluations of their subcircuits.
-/

/-- Evaluates a Boolean circuit on a truth assignment to its input variables. -/
def boolean_circuit_eval {n : Nat} (c : BooleanCircuit n) (x : Fin n → Bool) : Bool :=
  match c with
  | BooleanCircuit.var i => x i
  | BooleanCircuit.const b => b
  | BooleanCircuit.not c' => !boolean_circuit_eval c' x
  | BooleanCircuit.and c₁ c₂ => boolean_circuit_eval c₁ x && boolean_circuit_eval c₂ x
  | BooleanCircuit.or c₁ c₂ => boolean_circuit_eval c₁ x || boolean_circuit_eval c₂ x
