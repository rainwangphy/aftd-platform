import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpEvalList
import AFTD.Kb.GameTheoryEconomics.CatchUpIccOneEqRangeToFinset
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqEvalList

/-!
# catch_up_value_icc_eq_eval

Topic: combinatorial_games   Node: dfa0aeef7a3f

The value of Catch-Up on {1, ..., N} equals the computable mirror evaluated on the list [1, ..., N]; this is what lets the kernel settle concrete N.
-/

/-- Catch-Up on {1, ..., N} through the computable mirror. -/
theorem catch_up_value_icc_eq_eval (N : ℕ) :
    catch_up_value (Finset.Icc 1 N) = catch_up_eval_list N (List.range' 1 N) 0 0 true := by
  rw [catch_up_icc_one_eq_range_toFinset, catch_up_value_eq_eval_list _ List.nodup_range',
    List.length_range']
