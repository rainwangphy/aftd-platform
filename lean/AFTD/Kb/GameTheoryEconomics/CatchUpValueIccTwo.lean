import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValuePair
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value_icc_two

Topic: combinatorial_games   Node: 7c616ba2818f

The game value of Catch-Up played on the interval Finset.Icc 1 2 = {1, 2} is CatchUpOutcome.win.
-/

/-- In Catch-Up played on {1, 2}, the first player wins. -/
theorem catch_up_value_icc_two :
    catch_up_value (Finset.Icc 1 2) = CatchUpOutcome.win :=
  catch_up_value_pair 1 2 (Nat.lt_succ_self 1)
