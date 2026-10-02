import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxEmpty
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqAuxFalse
import AFTD.Kb.GameTheoryEconomics.CatchUpValueIccZero

/-!
# catch_up_value_aux_icc_zero_initial

Topic: combinatorial_games   Node: da6bcb75505d

In Catch-Up on the empty interval {1, ..., 0}, the auxiliary game value from scores 0, 0 is draw.
-/

/-- In Catch-Up on the empty interval Finset.Icc 1 0, Player 1's auxiliary value from equal scores 0 is draw. -/
theorem catch_up_value_aux_icc_zero_initial :
    catch_up_value_aux (Finset.Icc 1 0) 0 0 false = CatchUpOutcome.draw := by
  rw [← catch_up_value_eq_aux_false, catch_up_value_icc_zero]
