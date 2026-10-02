import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqLoss

/-!
# catch_up_best_map_ne_loss_iff

Topic: combinatorial_games   Node: 4a9087394811

The best outcome over a mapped list is not a loss if and only if some element maps to something other than a loss.
-/

/-- `best` over a mapped list is not a loss iff some element does not map to a loss. -/
theorem catch_up_best_map_ne_loss_iff {α : Type*} (l : List α) (c : α → CatchUpOutcome) :
    CatchUpOutcome.best (l.map c) ≠ .loss ↔ ∃ x ∈ l, c x ≠ .loss := by
  rw [Ne, catch_up_outcome_best_eq_loss]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall,
    exists_prop]
