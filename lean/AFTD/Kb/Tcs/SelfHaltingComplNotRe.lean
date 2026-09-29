import AFTD.Prelude
import AFTD.Kb.Tcs.NotReComplOfReAndNotComputable
import AFTD.Kb.Tcs.SelfHaltingProblemRe
import AFTD.Kb.Tcs.SelfHaltingProblemUndecidable

/-!
# self_halting_compl_not_re

Topic: computability   Node: 18954e079701

The complement of the diagonal halting problem is not recursively enumerable.
-/

/-- The complement of the diagonal halting problem is not recursively enumerable. -/
theorem self_halting_compl_not_re : ¬REPred (fun c : Nat.Partrec.Code => ¬(Nat.Partrec.Code.eval c (Encodable.encode c)).Dom) := not_re_compl_of_re_and_not_computable self_halting_problem_re self_halting_problem_undecidable
