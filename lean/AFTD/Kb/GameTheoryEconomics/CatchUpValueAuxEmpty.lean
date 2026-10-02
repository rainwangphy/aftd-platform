import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux

/-!
# catch_up_value_aux_empty

Topic: combinatorial_games   Node: 9670aa2af0a6

In a Catch-Up position with an empty set of remaining pieces, the game value for the mover is a win if the mover's score is strictly greater than the opponent's score, a loss if the mover's score is strictly less than the opponent's score, and a draw if the scores are equal, regardless of the isFirstMove flag.
-/

/-- In a Catch-Up position with no remaining pieces, the value is win if ahead, loss if behind, and draw if tied. -/
theorem catch_up_value_aux_empty (s_me s_opp : ℕ) (isFirstMove : Bool) :
    catch_up_value_aux ∅ s_me s_opp isFirstMove =
      if s_me > s_opp then CatchUpOutcome.win
      else if s_opp > s_me then CatchUpOutcome.loss
      else CatchUpOutcome.draw := by
  rw [catch_up_value_aux.eq_def]
  simp
