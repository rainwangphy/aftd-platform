import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpSearch
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpValueIccEqEval
import AFTD.Kb.GameTheoryEconomics.CatchUpSearchEq
import AFTD.Kb.GameTheoryEconomics.CatchUpEvalList

/-!
# catch_up_value_icc_eq_draw_of_search

Topic: combinatorial_games   Node: 1c9337e2c6f9

If the pruned search on [1, ..., N] from scores 0, 0 at the opening move finds no forced win for the first player but finds that the first player can avoid losing, then Catch-Up on {1, ..., N} is a draw.
-/

/-- Catch-Up on {1,...,N} is a draw when the search finds no forced win and no forced loss. -/
theorem catch_up_value_icc_eq_draw_of_search (N : ℕ)
    (hw : catch_up_search N (List.range' 1 N) 0 0 true true = false)
    (hl : catch_up_search N (List.range' 1 N) 0 0 true false = true) :
    catch_up_value (Finset.Icc 1 N) = .draw := by
  rw [catch_up_value_icc_eq_eval]
  have h := catch_up_search_eq N (List.range' 1 N) 0 0 true
  have hnw : catch_up_eval_list N (List.range' 1 N) 0 0 true ≠ .win := by
    intro e; rw [← h.1, hw] at e; exact Bool.false_ne_true e
  have hnl := h.2.1 hl
  cases hv : catch_up_eval_list N (List.range' 1 N) 0 0 true
  · exact absurd hv hnw
  · exact absurd hv hnl
  · rfl
