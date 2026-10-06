import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_outcome_eq_draw_iff

Topic: combinatorial_games   Node: 6328d15aba62

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

An outcome in CatchUpOutcome is a draw if and only if it is neither a win nor a loss.
-/

/-- An outcome in CatchUpOutcome is a draw if and only if it is neither a win nor a loss. -/
theorem catch_up_outcome_eq_draw_iff (o : CatchUpOutcome) :
    o = CatchUpOutcome.draw ↔ o ≠ CatchUpOutcome.win ∧ o ≠ CatchUpOutcome.loss := by
  cases o <;> simp
