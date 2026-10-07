import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqAuxFalse
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxZeroZero
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqLoss
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNegEqLossIff
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value_eq_loss_iff

Topic: combinatorial_games   Node: 748781cd6302

Provenance: formalization of a published result. Source: Catch-Up: A Game in Which the Lead Alternates (2015)

For any nonempty finite set S of natural numbers, the game value catch_up_value S is CatchUpOutcome.loss if and only if for every element x ∈ S, the second player wins from the resulting position, i.e., catch_up_value_aux (S.erase x) 0 x false = CatchUpOutcome.win.
-/

/-- Characterization of loss in Catch-Up: Player 1 loses if and only if Player 2 wins after every opening move. -/
theorem catch_up_value_eq_loss_iff (S : Finset ℕ) (hS : S.Nonempty) :
    catch_up_value S = CatchUpOutcome.loss ↔
      ∀ x ∈ S, catch_up_value_aux (S.erase x) 0 x false = CatchUpOutcome.win := by
  rw [catch_up_value_eq_aux_false, catch_up_value_aux_zero_zero S hS,
    catch_up_outcome_best_eq_loss]
  simp [catch_up_outcome_neg_eq_loss_iff]
