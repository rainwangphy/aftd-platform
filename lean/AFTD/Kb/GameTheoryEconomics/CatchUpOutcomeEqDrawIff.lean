import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_outcome_eq_draw_iff

Topic: combinatorial_games   Node: 6328d15aba62

An outcome in CatchUpOutcome is a draw if and only if it is neither a win nor a loss.
-/

/-- An outcome in CatchUpOutcome is a draw if and only if it is neither a win nor a loss. -/
theorem catch_up_outcome_eq_draw_iff (o : CatchUpOutcome) :
    o = CatchUpOutcome.draw ↔ o ≠ CatchUpOutcome.win ∧ o ≠ CatchUpOutcome.loss := by
  cases o <;> simp
