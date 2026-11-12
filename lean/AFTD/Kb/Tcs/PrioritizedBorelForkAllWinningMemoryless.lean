import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkAllWinningGame
import AFTD.Kb.Tcs.PrioritizedBorelForkAllWinningStrategy
import AFTD.Kb.Tcs.PrioritizedBorelHighestRecurrentIndex
import AFTD.Kb.Tcs.HasWinningStrategyInMem
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.FiniteMemoryStrategy

/-!
# prioritized_borel_fork_all_winning_memoryless

Topic: automata   Node: 5bd17fc073d4

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

The all-winning fork game has a winning strategy using one memory state.
-/

theorem prioritized_borel_fork_all_winning_memoryless : HasWinningStrategyInMem prioritized_borel_fork_all_winning_game 1 := by
  refine ⟨BorelGamePlayer.Eve, Unit, inferInstance, by simp, prioritized_borel_fork_all_winning_strategy, ?_⟩
  intro play _ _ _ _
  have hf : ∀ n, 1 ≤ (play n).prio.val + 1 ∧ (play n).prio.val + 1 ≤ 3 := by
    intro n
    have h := (play n).prio.isLt
    omega
  obtain ⟨I, hpos, hbound, hrec, N0, hmax⟩ :=
    prioritized_borel_highest_recurrent_index 3 (fun n => (play n).prio.val + 1) hf
  let p : Fin 3 := ⟨I - 1, by omega⟩
  refine ⟨p, ?_, ?_, by simp [prioritized_borel_fork_all_winning_game]⟩
  · apply Filter.frequently_atTop.mpr
    intro N
    obtain ⟨n, hn, heq⟩ := hrec N
    refine ⟨n, hn, ?_⟩
    apply Fin.ext
    dsimp [p]
    omega
  · intro q hq hfreq
    obtain ⟨n, hn, heq⟩ := Filter.frequently_atTop.mp hfreq N0
    have hh := hmax n hn
    have hp : p.val < q.val := hq
    have heqval := congrArg Fin.val heq
    dsimp [p] at hp
    omega
