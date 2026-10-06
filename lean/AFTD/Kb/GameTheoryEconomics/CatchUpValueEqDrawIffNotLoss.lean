import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNegEqWinIff
import AFTD.Kb.GameTheoryEconomics.CatchUpValueEqAuxFalse
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxZeroZero
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqWin
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeEqDrawIff
import AFTD.Kb.GameTheoryEconomics.CatchUpValue
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux

/-!
# catch_up_value_eq_draw_iff_not_loss

Topic: combinatorial_games   Node: 7ded50731067

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

The outcome of Catch-Up on a nonempty set S is a draw if and only if Player 1 does not lose from the initial position and Player 2 does not lose after any opening move from S.
-/

/-- For a nonempty set of pieces S, the outcome of Catch-Up is a draw if and only if Player 1 does not lose from the initial position and Player 2 does not lose after any first move x chosen from S. -/
theorem catch_up_value_eq_draw_iff_not_loss (S : Finset ℕ) (hS : S.Nonempty) :
    catch_up_value S = CatchUpOutcome.draw ↔
      (catch_up_value_aux S 0 0 false ≠ CatchUpOutcome.loss ∧
       ∀ x ∈ S, catch_up_value_aux (S.erase x) 0 x false ≠ CatchUpOutcome.loss) := by
  rw [catch_up_value_eq_aux_false]
  rw [catch_up_outcome_eq_draw_iff]
  have h_win : (catch_up_value_aux S 0 0 false = CatchUpOutcome.win) ↔
      ∃ x ∈ S, catch_up_value_aux (S.erase x) 0 x false = CatchUpOutcome.loss := by
    rw [catch_up_value_aux_zero_zero S hS]
    rw [catch_up_outcome_best_eq_win]
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and, Subtype.exists,
      exists_prop, catch_up_outcome_neg_eq_win_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    intro x hx h_loss
    apply h1
    rw [h_win]
    exact ⟨x, hx, h_loss⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    intro h_w
    rw [h_win] at h_w
    rcases h_w with ⟨x, hx, h_loss⟩
    exact h2 x hx h_loss
