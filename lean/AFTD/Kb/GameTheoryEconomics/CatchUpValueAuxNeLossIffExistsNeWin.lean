import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxZeroZero
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqLoss
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNeg
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value_aux_ne_loss_iff_exists_ne_win

Topic: combinatorial_games   Node: 4b5a5d4205fe

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

For any nonempty finite set S of pieces, Player 1 does not get outcome loss from equal scores 0 if and only if there exists an opening move x in S after which Player 2 does not get outcome win.
-/

/-- Player 1 does not lose from the initial position with equal scores 0 if and only if there exists an opening move after which Player 2 does not win. -/
theorem catch_up_value_aux_ne_loss_iff_exists_ne_win (S : Finset ℕ) (hS : S.Nonempty) :
    catch_up_value_aux S 0 0 false ≠ CatchUpOutcome.loss ↔
      ∃ x ∈ S, catch_up_value_aux (S.erase x) 0 x false ≠ CatchUpOutcome.win := by
  rw [catch_up_value_aux_zero_zero S hS]
  rw [ne_eq, catch_up_outcome_best_eq_loss]
  have h_neg (o : CatchUpOutcome) : o.neg = CatchUpOutcome.loss ↔ o = CatchUpOutcome.win := by
    cases o <;> decide
  simp [h_neg]
