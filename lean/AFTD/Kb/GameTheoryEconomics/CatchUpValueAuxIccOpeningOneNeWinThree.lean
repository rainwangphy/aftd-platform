import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpOutcome
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxIccOpeningOneNeWinIff
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAuxSingleton

/-!
# catch_up_value_aux_icc_opening_one_ne_win_three

Topic: combinatorial_games   Node: b2a25d078832

Provenance: helper lemma. step towards catch_up_value_aux_icc_opening_one_ne_win (Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates, 2015, Sec. 3.1))

In Catch-Up on {1, 2, 3}, Player 2 does not win after Player 1 opens with 1.
-/

/-- In Catch-Up on {1, 2, 3}, Player 2 does not win after Player 1 opens with 1. -/
theorem catch_up_value_aux_icc_opening_one_ne_win_three :
    catch_up_value_aux ((Finset.Icc 1 3).erase 1) 0 1 false ≠ CatchUpOutcome.win := by
  rw [catch_up_value_aux_icc_opening_one_ne_win_iff 3 (by norm_num)]
  intro y hy
  simp only [Finset.mem_erase, Finset.mem_Icc] at hy
  rcases show y = 2 ∨ y = 3 by omega with rfl | rfl
  · have hset : ((Finset.Icc 1 3).erase 1).erase 2 = {3} := by decide
    rw [hset, catch_up_value_aux_singleton]
    decide
  · have hset : ((Finset.Icc 1 3).erase 1).erase 3 = {2} := by decide
    rw [hset, catch_up_value_aux_singleton]
    decide
