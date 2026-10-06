import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEmpty
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value_icc_zero

Topic: combinatorial_games   Node: d1b973b8b187

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

In Catch-Up played on the empty interval {1, ..., 0}, the game value is a draw.
-/

/-- In Catch-Up played on the empty interval {1, ..., 0}, the game value is a draw. -/
theorem catch_up_value_icc_zero :
    catch_up_value (Finset.Icc 1 0) = CatchUpOutcome.draw := by
  rw [Finset.Icc_eq_empty_of_lt (by decide)]
  exact catch_up_value_empty
