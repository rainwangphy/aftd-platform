import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge

/-!
# prioritized_borel_fork_is_legal

Topic: automata   Node: 472aeb57f878

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

The legal edges of the three-state fork subarena, including both q self-loop directions and the q-to-hat-to-p-to-q excursion.
-/

def prioritized_borel_fork_is_legal (e : PrioritizedBorelForkEdge) : Prop :=
  (e.src = 0 ∧ e.dst = 0 ∧ e.prio = 0) ∨
  (e.src = 0 ∧ e.dir = false ∧ e.dst = 1 ∧ e.prio = 0) ∨
  (e.src = 1 ∧ e.dir = false ∧ e.dst = 2 ∧ e.prio = 0) ∨
  (e.src = 2 ∧ e.dst = 0 ∧
    ((e.dir = true ∧ e.prio = 1) ∨ (e.dir = false ∧ e.prio = 2)))
