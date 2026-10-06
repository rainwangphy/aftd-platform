import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux

/-!
# catch_up_value_empty

Topic: combinatorial_games   Node: 5038a5f26674

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

The value of Catch-Up on an empty set of pieces is a draw.
-/

/-- The value of Catch-Up played on the empty set of pieces is a draw. -/
theorem catch_up_value_empty :
    catch_up_value ∅ = CatchUpOutcome.draw := by
  unfold catch_up_value
  rw [catch_up_value_aux.eq_def]
  simp
