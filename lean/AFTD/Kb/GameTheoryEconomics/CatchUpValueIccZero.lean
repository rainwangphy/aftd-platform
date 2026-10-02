import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEmpty
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value_icc_zero

Topic: combinatorial_games   Node: d1b973b8b187

In Catch-Up played on the empty interval {1, ..., 0}, the game value is a draw.
-/

/-- In Catch-Up played on the empty interval {1, ..., 0}, the game value is a draw. -/
theorem catch_up_value_icc_zero :
    catch_up_value (Finset.Icc 1 0) = CatchUpOutcome.draw := by
  rw [Finset.Icc_eq_empty_of_lt (by decide)]
  exact catch_up_value_empty
