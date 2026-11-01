import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctFeasibleNat
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctValues

/-!
# efx_three_bonus_distinct_no_0_nat

Topic: fair_division   Node: 86c59379c807

Provenance: helper lemma. Finite obstruction to the distinct-recipient exchange route for OP-7, experiments 11403, 11405 and 11406.

No feasible allocation in the specified natural matrix gives old good 0 to agent 0.
-/

theorem efx_three_bonus_distinct_no_0_nat (σ : Fin 7 → Fin 4) (h : σ 0 = 0) : ¬ efx_three_bonus_distinct_feasible_nat σ := by
  -- With item 0 fixed to agent 0, the remaining six owners form a finite space;
  -- decide checks all 4^6 = 4096 cases against the feasible predicate.
  have key : ∀ a b c d e f : Fin 4, ¬ efx_three_bonus_distinct_feasible_nat ![0, a, b, c, d, e, f] := by
    unfold efx_three_bonus_distinct_feasible_nat
    decide
  have hσ : σ = ![0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6] := by
    funext i
    fin_cases i <;> simp [h]
  rw [hσ]
  exact key _ _ _ _ _ _
