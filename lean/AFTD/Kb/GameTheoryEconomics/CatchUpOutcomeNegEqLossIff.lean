import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNeg

/-!
# catch_up_outcome_neg_eq_loss_iff

Topic: combinatorial_games   Node: a4dc8e0f87d3

Provenance: helper lemma. folklore

Negating a Catch-Up outcome yields a loss if and only if the original outcome is a win.
-/

/-- Negating a Catch-Up outcome yields a loss if and only if the original outcome was a win. -/
theorem catch_up_outcome_neg_eq_loss_iff (o : CatchUpOutcome) :
    o.neg = CatchUpOutcome.loss ↔ o = CatchUpOutcome.win := by
  cases o <;> simp [CatchUpOutcome.neg]
