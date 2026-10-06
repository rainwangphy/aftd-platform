import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxIccEraseNeLossIff

/-!
# catch_up_value_aux_icc_erase_ne_loss_of_ge

Topic: combinatorial_games   Node: f4bb6324f0e6

Provenance: helper lemma. step towards catch_up_value_aux_icc_after_opening_ne_loss (Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates, 2015, Sec. 3.1))

In Catch-Up on {1, ..., N} with even triangular sum, if Player 2 has a response y ≥ x such that Player 1 does not win from the resulting position with scores (x, y), then Player 2 does not lose after opening move x.
-/

/-- In Catch-Up on {1, ..., N} with even triangular sum, if Player 2 has a response y ≥ x such that Player 1 does not win from the resulting position with scores (x, y), then Player 2 does not lose after opening move x. -/
theorem catch_up_value_aux_icc_erase_ne_loss_of_ge (N : ℕ) (h_even : Even (N * (N + 1) / 2))
    (x y : ℕ) (hx : x ∈ Finset.Icc 1 N) (hy : y ∈ (Finset.Icc 1 N).erase x) (hge : x ≤ y)
    (h : catch_up_value_aux (((Finset.Icc 1 N).erase x).erase y) x y false ≠ CatchUpOutcome.win) :
    catch_up_value_aux ((Finset.Icc 1 N).erase x) 0 x false ≠ CatchUpOutcome.loss := by
  rw [catch_up_value_aux_icc_erase_ne_loss_iff N h_even x hx]
  refine ⟨y, hy, ?_⟩
  simp [hge, h]
