import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctFeasibleNat
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctValues

/-!
# efx_three_bonus_distinct_no_1_nat

Topic: fair_division   Node: 2f33886b1760

Provenance: helper lemma. Finite obstruction to the distinct-recipient exchange route for OP-7, experiments 11403, 11405 and 11406.

No feasible allocation in the specified natural matrix gives old good 0 to agent 1.
-/

theorem efx_three_bonus_distinct_no_1_nat (σ : Fin 7 → Fin 4) (h : σ 0 = 1) : ¬ efx_three_bonus_distinct_feasible_nat σ := by
  have hp : σ = ![1, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6] := by
    funext i
    fin_cases i
    · exact h
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  rw [hp]
  generalize σ 1 = b, σ 2 = c, σ 3 = d, σ 4 = e, σ 5 = f, σ 6 = g
  revert b c d e f g
  unfold efx_three_bonus_distinct_feasible_nat efx_three_bonus_distinct_values
  decide +kernel
