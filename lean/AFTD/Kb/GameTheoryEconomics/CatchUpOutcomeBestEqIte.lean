import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqWin
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqDraw
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqLoss

/-!
# catch_up_outcome_best_eq_ite

Topic: combinatorial_games   Node: 12a0a3024d7f

The best outcome of a list depends only on which outcomes occur in it: win if a win occurs, otherwise draw if a draw occurs, otherwise loss.
-/

/-- `best` is win if a win occurs, else draw if a draw occurs, else loss. -/
theorem catch_up_outcome_best_eq_ite (os : List CatchUpOutcome) :
    CatchUpOutcome.best os =
      if CatchUpOutcome.win ∈ os then .win
      else if CatchUpOutcome.draw ∈ os then .draw else .loss := by
  by_cases hw : CatchUpOutcome.win ∈ os
  · rw [if_pos hw]; exact (catch_up_outcome_best_eq_win os).2 hw
  · rw [if_neg hw]
    by_cases hd : CatchUpOutcome.draw ∈ os
    · rw [if_pos hd]; exact (catch_up_outcome_best_eq_draw os).2 ⟨hw, hd⟩
    · rw [if_neg hd]
      refine (catch_up_outcome_best_eq_loss os).2 ?_
      intro o ho
      cases o
      · exact absurd ho hw
      · rfl
      · exact absurd ho hd
