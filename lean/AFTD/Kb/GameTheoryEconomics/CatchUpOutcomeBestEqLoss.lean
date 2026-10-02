import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBest
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqWin
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqDraw

/-!
# catch_up_outcome_best_eq_loss

Topic: combinatorial_games   Node: 2da88c2dc425

Under Catch-Up's best-outcome aggregation on a list of outcomes, the aggregated outcome is a loss if and only if every outcome in the list is a loss.
-/

/-- The aggregated outcome of a list under CatchUpOutcome.best is a loss if and only if every outcome in the list is a loss. -/
theorem catch_up_outcome_best_eq_loss (os : List CatchUpOutcome) :
    CatchUpOutcome.best os = CatchUpOutcome.loss ↔ ∀ o ∈ os, o = CatchUpOutcome.loss := by
  have h_loss (o : CatchUpOutcome) : o = CatchUpOutcome.loss ↔ o ≠ CatchUpOutcome.win ∧ o ≠ CatchUpOutcome.draw := by
    cases o <;> simp
  rw [h_loss]
  change (¬ CatchUpOutcome.best os = CatchUpOutcome.win) ∧ (¬ CatchUpOutcome.best os = CatchUpOutcome.draw) ↔ _
  rw [catch_up_outcome_best_eq_win, catch_up_outcome_best_eq_draw]
  constructor
  · rintro ⟨h1, h2⟩ o ho
    have hne_win : o ≠ CatchUpOutcome.win := by
      rintro rfl
      exact h1 ho
    have hne_draw : o ≠ CatchUpOutcome.draw := by
      rintro rfl
      apply h2
      exact ⟨h1, ho⟩
    rw [h_loss]
    exact ⟨hne_win, hne_draw⟩
  · intro h
    constructor
    · intro hwin
      have := h CatchUpOutcome.win hwin
      contradiction
    · rintro ⟨-, hdraw⟩
      have := h CatchUpOutcome.draw hdraw
      contradiction
