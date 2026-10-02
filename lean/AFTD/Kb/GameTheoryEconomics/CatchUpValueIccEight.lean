import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueIccEqEval

/-!
# catch_up_value_icc_eight

Topic: combinatorial_games   Node: a0bc50c8be43

Catch-Up on {1, ..., 8} is a draw under optimal play (the case N = 8 of the Catch-Up conjecture), evaluated by the Lean kernel.
-/

/-- Catch-Up on {1,...,8} is a draw (kernel-checked). -/
theorem catch_up_value_icc_eight : catch_up_value (Finset.Icc 1 8) = CatchUpOutcome.draw := by
  rw [catch_up_value_icc_eq_eval]; decide +kernel
