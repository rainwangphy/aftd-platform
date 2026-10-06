import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNeg

/-!
# catch_up_outcome_neg_eq_win_iff

Topic: combinatorial_games   Node: 19289ac1acf9

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

Negating an outcome yields a win if and only if the original outcome was a loss.
-/

/-- Negating an outcome in CatchUpOutcome yields a win if and only if the original outcome was a loss. -/
theorem catch_up_outcome_neg_eq_win_iff (o : CatchUpOutcome) :
    o.neg = CatchUpOutcome.win ↔ o = CatchUpOutcome.loss := by
  cases o <;> decide
