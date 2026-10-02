import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqWin

/-!
# catch_up_best_map_eq_win_iff

Topic: combinatorial_games   Node: 25864a82e49a

The best outcome over a mapped list is a win if and only if some element maps to a win.
-/

/-- `best` over a mapped list is a win iff some element maps to a win. -/
theorem catch_up_best_map_eq_win_iff {α : Type*} (l : List α) (c : α → CatchUpOutcome) :
    CatchUpOutcome.best (l.map c) = .win ↔ ∃ x ∈ l, c x = .win := by
  rw [catch_up_outcome_best_eq_win, List.mem_map]
