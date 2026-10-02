import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNeg
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest

/-!
# catch_up_value_aux

Topic: combinatorial_games   Node: ccb7e972bd2f

The game value of a Catch-Up position for the player about to move. If nothing remains, compare scores. If even all remaining numbers cannot bring the mover level with the opponent, the mover loses. Otherwise the mover picks a number x; on the opening move, or if the mover's score reaches at least the opponent's, the turn passes (value negated); if still strictly behind, the same player picks again. The mover takes the best outcome over all choices.
-/

/-- Value of a Catch-Up position under optimal play, for the player about to act: `remaining` numbers are untaken, `s_me`/`s_opp` are the scores, `isFirstMove` marks the opening move, where exactly one number is taken. Otherwise the mover keeps taking numbers while strictly behind and the turn passes once they reach at least the opponent's score; a mover who cannot catch up even with everything left loses. -/
noncomputable def catch_up_value_aux (remaining : Finset ℕ) (s_me s_opp : ℕ) (isFirstMove : Bool) : CatchUpOutcome :=
  if remaining = ∅ then
    if s_me > s_opp then .win
    else if s_opp > s_me then .loss
    else .draw
  else
    if s_me + remaining.sum (fun x => x) < s_opp then
      .loss
    else
      let moves := remaining.attach.toList
      let outcomes := moves.map (fun ⟨x, _⟩ =>
        let s_me' := s_me + x
        let remaining' := remaining.erase x
        if isFirstMove then
          (catch_up_value_aux remaining' s_opp s_me' false).neg
        else
          if s_me' ≥ s_opp then
            (catch_up_value_aux remaining' s_opp s_me' false).neg
          else
            catch_up_value_aux remaining' s_me' s_opp false)
      CatchUpOutcome.best outcomes
termination_by remaining.card
decreasing_by
  all_goals
    simpa using Finset.card_erase_lt_of_mem ‹_›
