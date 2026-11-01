import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctNo0Nat
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctNo1Nat
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctNo2Nat
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctNo3Nat
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctFeasibleNat

/-!
# efx_three_bonus_distinct_no_nat

Topic: fair_division   Node: b941e8ced790

Provenance: helper lemma. Finite obstruction to the distinct-recipient exchange route for OP-7, experiments 11403, 11405 and 11406.

No assignment in the explicit matrix simultaneously keeps old and bonus recipients respectively distinct, satisfies EFX, and preserves every old utility.
-/

theorem efx_three_bonus_distinct_no_nat (σ : Fin 7 → Fin 4) : ¬ efx_three_bonus_distinct_feasible_nat σ := by
  have h0 : σ 0 = 0 ∨ σ 0 = 1 ∨ σ 0 = 2 ∨ σ 0 = 3 := by omega
  rcases h0 with h | h | h | h
  · exact efx_three_bonus_distinct_no_0_nat σ h
  · exact efx_three_bonus_distinct_no_1_nat σ h
  · exact efx_three_bonus_distinct_no_2_nat σ h
  · exact efx_three_bonus_distinct_no_3_nat σ h
