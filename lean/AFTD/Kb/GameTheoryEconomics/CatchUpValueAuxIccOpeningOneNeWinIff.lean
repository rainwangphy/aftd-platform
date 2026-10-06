import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeBestEqWin
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcomeNegEqWinIff

/-!
# catch_up_value_aux_icc_opening_one_ne_win_iff

Topic: combinatorial_games   Node: 1794badce5b7

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

When N ≥ 3, Player 2 does not win after Player 1 opens with 1 iff for every response y from {2, ..., N}, Player 1 does not lose from the resulting position with scores (1, y).
-/

/-- When N ≥ 3, in the position after Player 1 opens with 1 from {1, ..., N}, Player 2 does not achieve outcome win if and only if for every response move y ∈ {2, ..., N}, Player 1 does not get outcome loss from the resulting position with scores (1, y). -/
theorem catch_up_value_aux_icc_opening_one_ne_win_iff (N : ℕ) (hN : 3 ≤ N) :
    catch_up_value_aux ((Finset.Icc 1 N).erase 1) 0 1 false ≠ CatchUpOutcome.win ↔
      ∀ y ∈ (Finset.Icc 1 N).erase 1,
        catch_up_value_aux (((Finset.Icc 1 N).erase 1).erase y) 1 y false ≠ CatchUpOutcome.loss := by
  have h2 : 2 ∈ (Finset.Icc 1 N).erase 1 := by
    rw [Finset.mem_erase, Finset.mem_Icc]
    omega
  have hne : (Finset.Icc 1 N).erase 1 ≠ ∅ := Finset.Nonempty.ne_empty ⟨2, h2⟩
  have hsum : ¬ (0 + ∑ x ∈ (Finset.Icc 1 N).erase 1, x < 1) := by
    have hle := Finset.single_le_sum (fun x _ => Nat.zero_le x) h2
    omega
  conv_lhs => rw [catch_up_value_aux]
  simp only [hne, ite_false, hsum]
  dsimp
  rw [not_congr (catch_up_outcome_best_eq_win _)]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and,
    Subtype.exists, not_exists]
  refine forall₂_congr (fun y hy => ?_)
  rw [Finset.mem_erase, Finset.mem_Icc] at hy
  have hge : 1 ≤ 0 + y := by omega
  rw [if_pos hge]
  simp only [zero_add]
  rw [not_congr (catch_up_outcome_neg_eq_win_iff _)]
