import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxNeLossIff
import AFTD.Kb.GameTheoryEconomics.CatchUpSumIccEraseGe
import AFTD.Kb.GameTheoryEconomics.CatchUpIccEraseNonempty
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome

/-!
# catch_up_value_aux_icc_erase_ne_loss_iff

Topic: combinatorial_games   Node: 951760d87a75

After Player 1 opens with x from {1, ..., N} (with even triangular sum), Player 2 does not lose if and only if there exists a response move y in {1, ..., N} \ {x} that avoids a win for Player 1 (if y ≥ x) or avoids a loss for Player 2 (if y < x).
-/

/-- In Catch-Up on {1, ..., N} with even triangular sum, Player 2 does not lose after opening move x if and only if there exists a valid non-losing response. -/
theorem catch_up_value_aux_icc_erase_ne_loss_iff (N : ℕ) (h_even : Even (N * (N + 1) / 2))
    (x : ℕ) (hx : x ∈ Finset.Icc 1 N) :
    catch_up_value_aux ((Finset.Icc 1 N).erase x) 0 x false ≠ CatchUpOutcome.loss ↔
      ∃ y ∈ (Finset.Icc 1 N).erase x,
        if y ≥ x then
          catch_up_value_aux (((Finset.Icc 1 N).erase x).erase y) x y false ≠ CatchUpOutcome.win
        else
          catch_up_value_aux (((Finset.Icc 1 N).erase x).erase y) y x false ≠ CatchUpOutcome.loss := by
  have hrem := catch_up_icc_erase_nonempty N h_even x hx
  have hsum_ge := catch_up_sum_icc_erase_ge N h_even x hx
  have hsum : ¬ 0 + ∑ y ∈ (Finset.Icc 1 N).erase x, y < x := by
    rw [Nat.zero_add]
    exact not_lt_of_ge hsum_ge
  have h := catch_up_value_aux_ne_loss_iff ((Finset.Icc 1 N).erase x) 0 x hrem hsum
  simp only [Nat.zero_add] at h
  exact h
