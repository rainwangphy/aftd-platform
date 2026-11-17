import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.PrioritizedBorelEncodedArenaForwardDeterministic
import AFTD.Kb.Tcs.PrioritizedBorelForwardDeterministicOneStateReduction
import AFTD.Kb.Tcs.HasWinningStrategyInMem
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# prioritized_borel_encoded_arena_wins_from_one_state

Topic: automata   Node: 3c4fb23b442e

Provenance: helper lemma. Block-encoded phase arena for arXiv:2611.10136, Conjecture 19.

If every one-state three-priority game has a winner using at most b memory states, then the phase-state encoded game has a winner using at most b memory states.
-/

theorem prioritized_borel_encoded_arena_wins_from_one_state {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3)
    (b : ℕ) (hone : ∀ H : PrioritizedBorelGame Unit 3, HasWinningStrategyInMem H b) :
    HasWinningStrategyInMem (enc1385Game G) b := by
  exact prioritized_borel_forward_deterministic_one_state_reduction _ b (prioritized_borel_encoded_arena_forward_deterministic G) hone
