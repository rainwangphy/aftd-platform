import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqAuxFalse
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxZeroZero
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqWin
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNegEqWinIff
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxEmpty
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxSingleton

/-!
# catch_up_value_singleton

Topic: combinatorial_games   Node: c565c795f167

For any strictly positive natural number x, the game value of Catch-Up played on the singleton set {x} is CatchUpOutcome.win.
-/

/-- In Catch-Up played on a single positive piece {x}, the first player wins. -/
theorem catch_up_value_singleton (x : ℕ) (hx : 0 < x) :
    catch_up_value {x} = CatchUpOutcome.win := by
  rw [catch_up_value_eq_aux_false]
  rw [catch_up_value_aux_singleton]
  simp [hx]
