import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkValid
import AFTD.Kb.Tcs.PrioritizedBorelForkConsistent
import AFTD.Kb.Tcs.PrioritizedBorelForkConsistentAppend
import AFTD.Kb.Tcs.PrioritizedBorelForkExitConsistent
import AFTD.Kb.Tcs.PrioritizedBorelForkExpand
import AFTD.Kb.Tcs.PrioritizedBorelForkExpandSnoc
import AFTD.Kb.Tcs.PrioritizedBorelForkSetup
import AFTD.Kb.Tcs.PrioritizedBorelForkStayConsistent
import AFTD.Kb.Tcs.PrioritizedBorelForkValidLengths
import AFTD.Kb.Tcs.PrioritizedBorelForkThreeStepBlock

/-!
# prioritized_borel_fork_valid_consistent

Topic: automata   Node: 317e26dbc182

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

Every valid hidden block history expands to an edge history consistent with the actual history-dependent p-owned choice function.
-/

theorem prioritized_borel_fork_valid_consistent (choice : List PrioritizedBorelForkEdge → Bool)
    {u h : List Bool}
    (hv : PrioritizedBorelForkValid
      (fun v k => choice (prioritized_borel_fork_expand v k ++ prioritized_borel_fork_setup)) u h) :
    prioritized_borel_fork_consistent choice [] (prioritized_borel_fork_expand u h) := by
  induction hv with
  | root => simp [prioritized_borel_fork_expand, prioritized_borel_fork_consistent]
  | @stay u h bit hv ih =>
      rw [prioritized_borel_fork_expand_snoc u h (prioritized_borel_fork_valid_lengths hv),
        prioritized_borel_fork_consistent_append]
      simp only [List.nil_append]
      exact ⟨ih, prioritized_borel_fork_stay_consistent choice _ bit⟩
  | @exit u h hv ih =>
      rw [prioritized_borel_fork_expand_snoc u h (prioritized_borel_fork_valid_lengths hv),
        prioritized_borel_fork_consistent_append]
      simp only [List.nil_append]
      exact ⟨ih, prioritized_borel_fork_exit_consistent choice _⟩
