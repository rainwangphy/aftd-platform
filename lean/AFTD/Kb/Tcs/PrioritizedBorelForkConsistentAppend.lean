import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkConsistent

/-!
# prioritized_borel_fork_consistent_append

Topic: automata   Node: 164fbd8b7138

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

Consistency of concatenated histories splits into consistency before and after the cut, with the preceding history passed to the second part.
-/

theorem prioritized_borel_fork_consistent_append (choice : List PrioritizedBorelForkEdge → Bool)
    (pre xs ys : List PrioritizedBorelForkEdge) :
    prioritized_borel_fork_consistent choice pre (xs ++ ys) ↔
      prioritized_borel_fork_consistent choice pre xs ∧
      prioritized_borel_fork_consistent choice (pre ++ xs) ys := by
  induction xs generalizing pre with
  | nil => simp [prioritized_borel_fork_consistent]
  | cons e es ih =>
      simp [prioritized_borel_fork_consistent, ih, List.append_assoc, and_assoc]
