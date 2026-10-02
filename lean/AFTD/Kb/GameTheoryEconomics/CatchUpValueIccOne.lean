import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueSingleton
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueIccEqEval

/-!
# catch_up_value_icc_one

Topic: combinatorial_games   Node: 0974dc7024e0

The game value of Catch-Up played on the interval Finset.Icc 1 1 is CatchUpOutcome.win.
-/

/-- The game value of Catch-Up played on the interval Finset.Icc 1 1 is CatchUpOutcome.win. -/
theorem catch_up_value_icc_one :
    catch_up_value (Finset.Icc 1 1) = CatchUpOutcome.win := by
  rw [catch_up_value_icc_eq_eval]; decide +kernel
