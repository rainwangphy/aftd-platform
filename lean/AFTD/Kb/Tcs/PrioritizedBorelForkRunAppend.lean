import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkRun
import AFTD.Kb.Tcs.PrioritizedBorelForkIsLegal

/-!
# prioritized_borel_fork_run_append

Topic: automata   Node: 29caab09eb65

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

Two finite legal fork runs can be concatenated when their intermediate states agree.
-/

theorem prioritized_borel_fork_run_append {q r s : Fin 3} {xs ys : List PrioritizedBorelForkEdge}
    (h : PrioritizedBorelForkRun q xs r) (h' : PrioritizedBorelForkRun r ys s) :
    PrioritizedBorelForkRun q (xs ++ ys) s := by
  induction h with
  | nil => simpa using h'
  | cons hlegal hsrc hrun ih =>
      simp only [List.cons_append]
      exact PrioritizedBorelForkRun.cons hlegal hsrc (ih h')
