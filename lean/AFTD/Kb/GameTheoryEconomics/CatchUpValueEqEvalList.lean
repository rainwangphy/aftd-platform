import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpEvalList
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxEqEvalList

/-!
# catch_up_value_eq_eval_list

Topic: combinatorial_games   Node: 9631b1236060

For a duplicate-free list l, the value of Catch-Up on the finset of l equals the computable mirror evaluated on l from scores 0, 0 at the opening move.
-/

/-- Catch-Up on the finset of a duplicate-free list, computed by the mirror. -/
theorem catch_up_value_eq_eval_list (l : List ℕ) (hl : l.Nodup) :
    catch_up_value l.toFinset = catch_up_eval_list l.length l 0 0 true :=
  catch_up_value_aux_eq_eval_list l.length l hl le_rfl 0 0 true
