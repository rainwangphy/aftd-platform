import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge
import AFTD.Kb.Tcs.PrioritizedBorelForkRun
import AFTD.Kb.Tcs.PrioritizedBorelForkConsistent
import AFTD.Kb.Tcs.PrioritizedBorelForkDecodeExpand
import AFTD.Kb.Tcs.PrioritizedBorelForkExpand
import AFTD.Kb.Tcs.PrioritizedBorelForkExpandDirections
import AFTD.Kb.Tcs.PrioritizedBorelForkExpandRun
import AFTD.Kb.Tcs.PrioritizedBorelForkFixedBranchMemoryFibers
import AFTD.Kb.Tcs.PrioritizedBorelForkHiddenDecode
import AFTD.Kb.Tcs.PrioritizedBorelForkSetup
import AFTD.Kb.Tcs.PrioritizedBorelForkValidConsistent
import AFTD.Kb.Tcs.PrioritizedBorelForkValidLengths
import AFTD.Kb.Tcs.PrioritizedBorelForkValid

/-!
# prioritized_borel_fork_strategy_fixed_branch

Topic: automata   Node: 168817efcbd2

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

For any history-dependent strategy and finite-memory assignment in the three-state fork arena, there are one infinite visible block sequence and one fixed memory value for which arbitrarily many distinct legal strategy-consistent runs ending at q and that memory value share prefixes of the sequence.
-/

theorem prioritized_borel_fork_strategy_fixed_branch {M : Type} [Fintype M]
    (choice : List PrioritizedBorelForkEdge → Bool) (memory : List PrioritizedBorelForkEdge → M) :
    ∃ f : ℕ → Bool, ∃ m : M, ∀ d, ∃ n, ∃ S : Finset (List Bool),
      d < S.card ∧
      (∀ h ∈ S,
        prioritized_borel_fork_consistent choice []
          (prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h) ∧
        memory (prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h) = m ∧
        PrioritizedBorelForkRun 0 (prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h) 0 ∧
        (prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h).map PrioritizedBorelForkEdge.dir =
          (List.ofFn (fun i : Fin n => f i)).flatMap (fun b => [false, false, b])) ∧
      (∀ h ∈ S, ∀ k ∈ S,
        prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) h =
          prioritized_borel_fork_expand (List.ofFn (fun i : Fin n => f i)) k → h = k) := by
  obtain ⟨f, m, hf⟩ := prioritized_borel_fork_fixed_branch_memory_fibers
    (fun u h => choice (prioritized_borel_fork_expand u h ++ prioritized_borel_fork_setup))
    (fun u h => memory (prioritized_borel_fork_expand u h))
  refine ⟨f, m, ?_⟩
  intro d
  obtain ⟨n, S, hcard, hvalid⟩ := hf d
  let u : List Bool := List.ofFn (fun i : Fin n => f i)
  refine ⟨n, S, hcard, ?_, ?_⟩
  · intro h hh
    obtain ⟨hv, hm⟩ := hvalid h hh
    exact ⟨prioritized_borel_fork_valid_consistent choice hv, hm, prioritized_borel_fork_expand_run u h,
      prioritized_borel_fork_expand_directions u h (prioritized_borel_fork_valid_lengths hv)⟩
  · intro h hh k hk heq
    have h1 := prioritized_borel_fork_decode_expand u h (prioritized_borel_fork_valid_lengths (hvalid h hh).1)
    have h2 := prioritized_borel_fork_decode_expand u k (prioritized_borel_fork_valid_lengths (hvalid k hk).1)
    change prioritized_borel_fork_expand u h = prioritized_borel_fork_expand u k at heq
    have he := congrArg prioritized_borel_fork_hidden_decode heq
    rw [h1, h2] at he
    exact he
