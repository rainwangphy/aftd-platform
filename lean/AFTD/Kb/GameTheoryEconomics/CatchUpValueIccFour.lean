import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueIccEqEval

/-!
# catch_up_value_icc_four

Topic: combinatorial_games   Node: 89d220212ec5

Catch-Up on {1, 2, 3, 4} is a draw under optimal play (the case N = 4 of the Catch-Up conjecture), evaluated by the Lean kernel.
-/

/-- Catch-Up on {1,2,3,4} is a draw (kernel-checked). -/
theorem catch_up_value_icc_four : catch_up_value (Finset.Icc 1 4) = CatchUpOutcome.draw := by
  rw [catch_up_value_icc_eq_eval]; decide +kernel
