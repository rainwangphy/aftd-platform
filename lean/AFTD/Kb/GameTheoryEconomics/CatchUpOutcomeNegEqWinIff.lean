import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNeg

/-!
# catch_up_outcome_neg_eq_win_iff

Topic: combinatorial_games   Node: 19289ac1acf9

Negating an outcome yields a win if and only if the original outcome was a loss.
-/

/-- Negating an outcome in CatchUpOutcome yields a win if and only if the original outcome was a loss. -/
theorem catch_up_outcome_neg_eq_win_iff (o : CatchUpOutcome) :
    o.neg = CatchUpOutcome.win ↔ o = CatchUpOutcome.loss := by
  cases o <;> decide
