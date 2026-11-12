import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge

/-!
# prioritized_borel_fork_consistent

Topic: automata   Node: 33207e72c2b5

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

A finite edge history is consistent with a history-dependent choice function when every p-owned edge uses the direction the function chooses from the preceding history.
-/

def prioritized_borel_fork_consistent (choice : List PrioritizedBorelForkEdge → Bool) :
    List PrioritizedBorelForkEdge → List PrioritizedBorelForkEdge → Prop
  | _, [] => True
  | pre, e :: es =>
      (e.src = 2 → e.dir = choice pre) ∧
      prioritized_borel_fork_consistent choice (pre ++ [e]) es
