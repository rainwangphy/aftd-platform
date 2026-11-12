import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkRun
import AFTD.Kb.Tcs.PrioritizedBorelForkConsistent
import AFTD.Kb.Tcs.PrioritizedBorelForkExpand
import AFTD.Kb.Tcs.PrioritizedBorelForkSetup
import AFTD.Kb.Tcs.PrioritizedBorelForkUnboundedSameMemory
import AFTD.Kb.Tcs.PrioritizedBorelForkValidConsistent
import AFTD.Kb.Tcs.PrioritizedBorelForkValid

/-!
# prioritized_borel_fork_strategy_obstruction

Topic: automata   Node: 635c95f7a27d

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

For any history-dependent strategy and any finite-memory assignment, arbitrarily many distinct legal strategy-consistent runs return to q on one visible finite branch and one memory value.
-/

theorem prioritized_borel_fork_strategy_obstruction {M : Type} [Fintype M]
    (choice : List PrioritizedBorelForkEdge → Bool) (memory : List PrioritizedBorelForkEdge → M)
    (d : ℕ) :
    ∃ u : List Bool, ∃ m : M, ∃ S : Finset (List Bool),
      d < S.card ∧
      (∀ h ∈ S,
        prioritized_borel_fork_consistent choice [] (prioritized_borel_fork_expand u h) ∧
        memory (prioritized_borel_fork_expand u h) = m ∧
        PrioritizedBorelForkRun 0 (prioritized_borel_fork_expand u h) 0 ∧
        (prioritized_borel_fork_expand u h).map PrioritizedBorelForkEdge.dir =
          u.flatMap (fun b => [false, false, b])) ∧
      (∀ h ∈ S, ∀ k ∈ S,
        prioritized_borel_fork_expand u h = prioritized_borel_fork_expand u k → h = k) := by
  obtain ⟨u, m, S, hc, hv, hinj⟩ := prioritized_borel_fork_unbounded_same_memory
    (fun H => choice (H ++ prioritized_borel_fork_setup)) memory d
  refine ⟨u, m, S, hc, ?_, hinj⟩
  intro h hh
  obtain ⟨hvalid, hmem, hrun, hdir⟩ := hv h hh
  exact ⟨prioritized_borel_fork_valid_consistent choice hvalid, hmem, hrun, hdir⟩
