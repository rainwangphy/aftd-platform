import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkIsLegal
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.BorelGamePlayer
import AFTD.Kb.Tcs.PrioritizedBorelForkEdge

/-!
# prioritized_borel_fork_all_winning_game

Topic: automata   Node: 725683a4dd3c

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2; the three-state fork subarena

The three-state fork arena with every priority branch set equal to the full branch space.
-/

def prioritized_borel_fork_all_winning_game : PrioritizedBorelGame (Fin 3) 3 where
  owner := fun pos => if pos.2 = 2 then BorelGamePlayer.Eve else BorelGamePlayer.Adam
  init_state := 0
  edges := {e | prioritized_borel_fork_is_legal ⟨e.source_state, e.dir, e.target_state, e.prio⟩}
  edges_outgoing := by
    intro v q
    fin_cases q
    · exact ⟨⟨v, 0, false, 0, 0⟩, by norm_num [prioritized_borel_fork_is_legal], rfl, rfl⟩
    · exact ⟨⟨v, 1, false, 0, 2⟩, by norm_num [prioritized_borel_fork_is_legal], rfl, rfl⟩
    · exact ⟨⟨v, 2, true, 1, 0⟩, by norm_num [prioritized_borel_fork_is_legal], rfl, rfl⟩
  winning_sets := fun _ => Set.univ
  winning_measurable := by intro i; exact MeasurableSet.univ
