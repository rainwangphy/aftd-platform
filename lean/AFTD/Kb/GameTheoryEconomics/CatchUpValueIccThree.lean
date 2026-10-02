import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueTripleDraw
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueIccEqEval

/-!
# catch_up_value_icc_three

Topic: combinatorial_games   Node: 1fd4506db3fc

The game value of Catch-Up played on the interval Finset.Icc 1 3 is CatchUpOutcome.draw.
-/

/-- The game value of Catch-Up played on the interval Finset.Icc 1 3 is CatchUpOutcome.draw. -/
theorem catch_up_value_icc_three :
    catch_up_value (Finset.Icc 1 3) = CatchUpOutcome.draw := by
  rw [catch_up_value_icc_eq_eval]; decide +kernel
