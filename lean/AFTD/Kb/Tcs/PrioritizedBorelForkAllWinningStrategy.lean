import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkAllWinningGame
import AFTD.Kb.Tcs.PrioritizedBorelForkIsLegal
import AFTD.Kb.Tcs.FiniteMemoryStrategy
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.BorelGamePlayer

/-!
# prioritized_borel_fork_all_winning_strategy

Topic: automata   Node: 21f4392a77ff

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

A memoryless strategy choosing the true-direction edge at the p-owned state of the all-winning fork game.
-/

def prioritized_borel_fork_all_winning_strategy : FiniteMemoryStrategy prioritized_borel_fork_all_winning_game BorelGamePlayer.Eve Unit where
  init_mem := ()
  update := fun _ _ => ()
  choice := fun _ v q => ⟨v, q, true, 1, 0⟩
  choice_edge := by
    intro m v q howner
    have hq : q = 2 := by
      have : (if q = 2 then BorelGamePlayer.Eve else BorelGamePlayer.Adam) =
          BorelGamePlayer.Eve := howner
      split_ifs at this with h
      · exact h
    subst q
    exact ⟨by norm_num [prioritized_borel_fork_all_winning_game, prioritized_borel_fork_is_legal], rfl, rfl⟩
