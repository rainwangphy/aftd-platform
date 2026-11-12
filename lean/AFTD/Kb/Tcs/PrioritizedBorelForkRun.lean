import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkIsLegal

/-!
# PrioritizedBorelForkRun

Topic: automata   Node: 4005cfde7534

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

A finite path in the fork arena whose edges are legal and have matching endpoints.
-/

inductive PrioritizedBorelForkRun : Fin 3 → List PrioritizedBorelForkEdge → Fin 3 → Prop
  | nil (q : Fin 3) : PrioritizedBorelForkRun q [] q
  | cons {q s : Fin 3} {e : PrioritizedBorelForkEdge} {es : List PrioritizedBorelForkEdge} :
      prioritized_borel_fork_is_legal e → e.src = q → PrioritizedBorelForkRun e.dst es s →
      PrioritizedBorelForkRun q (e :: es) s
