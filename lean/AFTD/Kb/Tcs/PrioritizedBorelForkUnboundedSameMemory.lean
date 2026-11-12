import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkRun
import AFTD.Kb.Tcs.PrioritizedBorelForkValid
import AFTD.Kb.Tcs.PrioritizedBorelForkDecodeExpand
import AFTD.Kb.Tcs.PrioritizedBorelForkExpand
import AFTD.Kb.Tcs.PrioritizedBorelForkExpandDirections
import AFTD.Kb.Tcs.PrioritizedBorelForkExpandRun
import AFTD.Kb.Tcs.PrioritizedBorelForkHiddenDecode
import AFTD.Kb.Tcs.PrioritizedBorelForkMemoryFiberUnbounded
import AFTD.Kb.Tcs.PrioritizedBorelForkValidLengths

/-!
# prioritized_borel_fork_unbounded_same_memory

Topic: automata   Node: 8e5c6eb1602e

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

For any history-dependent excursion choice and finite-memory assignment, arbitrarily many distinct legal runs from q to q share their visible directions and memory value, and each excursion follows the choice function.
-/

theorem prioritized_borel_fork_unbounded_same_memory {M : Type} [Fintype M]
    (choice : List PrioritizedBorelForkEdge → Bool) (memory : List PrioritizedBorelForkEdge → M)
    (d : ℕ) :
    ∃ u : List Bool, ∃ m : M, ∃ S : Finset (List Bool),
      d < S.card ∧
      (∀ h ∈ S,
        PrioritizedBorelForkValid (fun v k => choice (prioritized_borel_fork_expand v k)) u h ∧
        memory (prioritized_borel_fork_expand u h) = m ∧
        PrioritizedBorelForkRun 0 (prioritized_borel_fork_expand u h) 0 ∧
        (prioritized_borel_fork_expand u h).map PrioritizedBorelForkEdge.dir =
          u.flatMap (fun b => [false, false, b])) ∧
      (∀ h ∈ S, ∀ k ∈ S,
        prioritized_borel_fork_expand u h = prioritized_borel_fork_expand u k → h = k) := by
  obtain ⟨u, m, S, hcard, hvalid⟩ := prioritized_borel_fork_memory_fiber_unbounded
    (fun v k => choice (prioritized_borel_fork_expand v k))
    (fun v k => memory (prioritized_borel_fork_expand v k)) d
  refine ⟨u, m, S, hcard, ?_, ?_⟩
  · intro h hh
    obtain ⟨hv, hm⟩ := hvalid h hh
    exact ⟨hv, hm, prioritized_borel_fork_expand_run u h,
      prioritized_borel_fork_expand_directions u h (prioritized_borel_fork_valid_lengths hv)⟩
  · intro h hh k hk heq
    have h1 := prioritized_borel_fork_decode_expand u h (prioritized_borel_fork_valid_lengths (hvalid h hh).1)
    have h2 := prioritized_borel_fork_decode_expand u k (prioritized_borel_fork_valid_lengths (hvalid k hk).1)
    have he := congrArg prioritized_borel_fork_hidden_decode heq
    simpa [h1, h2] using he
