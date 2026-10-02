import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqAuxFalse
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxZeroZero
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqWin
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNegEqWinIff
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux

/-!
# catch_up_value_eq_win_iff

Topic: combinatorial_games   Node: 65b1d03aa88a

For any nonempty finite set S of natural numbers, the game value catch_up_value S is CatchUpOutcome.win if and only if there exists some element x ∈ S such that the second player loses from the resulting position, i.e., catch_up_value_aux (S.erase x) 0 x false = CatchUpOutcome.loss.
-/

/-- The game value of Catch-Up on a nonempty set S is a win for the first player if and only if there is an opening move x in S leading to a loss for the second player. -/
theorem catch_up_value_eq_win_iff (S : Finset ℕ) (hS : S.Nonempty) :
    catch_up_value S = CatchUpOutcome.win ↔
      ∃ x ∈ S, catch_up_value_aux (S.erase x) 0 x false = CatchUpOutcome.loss := by
  rw [catch_up_value_eq_aux_false, catch_up_value_aux_zero_zero S hS,
    catch_up_outcome_best_eq_win]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and,
    catch_up_outcome_neg_eq_win_iff]
  exact ⟨fun ⟨⟨x, hx⟩, h⟩ => ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, h⟩⟩
