import AFTD.Prelude

/-!
# self_halting_problem_re

Topic: computability   Node: 0b4dc027f2c7

The diagonal halting problem, consisting of codes c such that c halts on its own code, is recursively enumerable.
-/

/-- The diagonal halting problem (self-halting problem) is recursively enumerable. -/
theorem self_halting_problem_re : REPred (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c (Encodable.encode c)).Dom) := (Nat.Partrec.Code.eval_part.comp Computable.id Computable.encode).dom_re
