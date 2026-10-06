import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxIccEraseNeLossIff

/-!
# catch_up_value_aux_icc_erase_max_ne_loss_iff

Topic: combinatorial_games   Node: 946296ad9f6b

Provenance: helper lemma. step towards catch_up_value_aux_icc_after_opening_ne_loss (Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates, 2015, Sec. 3.1))

After Player 1 opens with N in Catch-Up on {1, ..., N} with even triangular sum and N > 0, every response y satisfies y < N, so Player 2 does not lose iff there is a response y such that Player 2 does not lose from the resulting position with scores (y, N).
-/

/-- After Player 1 opens with N in Catch-Up on {1, ..., N} with even triangular sum and N > 0, every response y satisfies y < N, so Player 2 does not lose iff there is a response y such that Player 2 does not lose from the resulting position with scores (y, N). -/
theorem catch_up_value_aux_icc_erase_max_ne_loss_iff (N : ℕ) (hN : 0 < N)
    (h_even : Even (N * (N + 1) / 2)) :
    catch_up_value_aux ((Finset.Icc 1 N).erase N) 0 N false ≠ CatchUpOutcome.loss ↔
      ∃ y ∈ (Finset.Icc 1 N).erase N,
        catch_up_value_aux (((Finset.Icc 1 N).erase N).erase y) y N false ≠ CatchUpOutcome.loss := by
  have hN_mem : N ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hN, le_rfl⟩
  rw [catch_up_value_aux_icc_erase_ne_loss_iff N h_even N hN_mem]
  apply exists_congr
  intro y
  apply and_congr_right
  intro hy
  rw [Finset.mem_erase, Finset.mem_Icc] at hy
  have h_not : ¬(y ≥ N) := not_le_of_gt (lt_of_le_of_ne hy.2.2 hy.1)
  rw [if_neg h_not]
