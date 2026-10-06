import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxFirstMoveEqOfEqScores
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux

/-!
# catch_up_value_eq_aux_false

Topic: combinatorial_games   Node: 27c37de35000

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

The game value catch_up_value S is equal to catch_up_value_aux S 0 0 false.
-/

/-- The outcome of Catch-Up on S equals the auxiliary game value starting at score (0, 0) with isFirstMove = false. -/
theorem catch_up_value_eq_aux_false (S : Finset ℕ) :
    catch_up_value S = catch_up_value_aux S 0 0 false := catch_up_value_aux_first_move_eq_of_eq_scores S 0
