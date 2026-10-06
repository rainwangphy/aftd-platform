import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNeg

/-!
# catch_up_outcome_neg_eq_draw_iff

Topic: combinatorial_games   Node: 1a7d918344ee

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

Negating an outcome yields a draw if and only if the original outcome is a draw.
-/

/-- Negating an outcome in CatchUpOutcome yields a draw if and only if the outcome is a draw. -/
theorem catch_up_outcome_neg_eq_draw_iff (o : CatchUpOutcome) :
    CatchUpOutcome.neg o = CatchUpOutcome.draw ↔ o = CatchUpOutcome.draw := by
  cases o <;> decide
