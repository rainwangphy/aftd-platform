import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxZeroZero
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqLoss
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNeg
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value_aux_ne_loss_of_ne_win

Topic: combinatorial_games   Node: 77b2534ee4ef

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

In Catch-Up from equal scores 0, if an opening move x in S leads to a position where the second player does not win, then the first player does not lose from the start.
-/

/-- If there is an opening move x in S after which Player 2 does not win, then Player 1 does not lose from the initial position with equal scores 0. -/
theorem catch_up_value_aux_ne_loss_of_ne_win (S : Finset ℕ) {x : ℕ} (hx : x ∈ S)
    (h : catch_up_value_aux (S.erase x) 0 x false ≠ CatchUpOutcome.win) :
    catch_up_value_aux S 0 0 false ≠ CatchUpOutcome.loss := by
  have hS : S.Nonempty := ⟨x, hx⟩
  rw [catch_up_value_aux_zero_zero S hS]
  intro h_loss
  rw [catch_up_outcome_best_eq_loss] at h_loss
  have h_in : (catch_up_value_aux (S.erase x) 0 x false).neg ∈
      S.attach.toList.map (fun ⟨y, _⟩ => (catch_up_value_aux (S.erase y) 0 y false).neg) := by
    refine List.mem_map.2 ⟨⟨x, hx⟩, ?_, rfl⟩
    simp
  have h_eq := h_loss _ h_in
  cases h_val : catch_up_value_aux (S.erase x) 0 x false with
  | win => exact h h_val
  | loss => rw [h_val] at h_eq; cases h_eq
  | draw => rw [h_val] at h_eq; cases h_eq
