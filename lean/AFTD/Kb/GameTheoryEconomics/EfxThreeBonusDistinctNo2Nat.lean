import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctFeasibleNat
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctValues

/-!
# efx_three_bonus_distinct_no_2_nat

Topic: fair_division   Node: 99234cc637b5

Provenance: helper lemma. Finite obstruction to the distinct-recipient exchange route for OP-7, experiments 11403, 11405 and 11406.

No feasible allocation in the specified natural matrix gives old good 0 to agent 2.
-/

theorem efx_three_bonus_distinct_no_2_nat (σ : Fin 7 → Fin 4) (h : σ 0 = 2) : ¬ efx_three_bonus_distinct_feasible_nat σ := by
  intro hf
  obtain ⟨h1, h2, h3, h4⟩ := hf
  -- old goods 1, 2, 3 do not go to agent 2, since old goods go to distinct agents
  have h01 : σ 1 ≠ 2 := by
    have := h1 0 1 (by decide)
    simpa [h, eq_comm] using this
  have h02 : σ 2 ≠ 2 := by
    have := h1 0 2 (by decide)
    simpa [h, eq_comm] using this
  have h03 : σ 3 ≠ 2 := by
    have := h1 0 3 (by decide)
    simpa [h, eq_comm] using this
  -- agent 2's utility: 18 from old good 0, nothing from old goods 1,2,3,
  -- and at most 17 + 1 + 1 from the bonuses
  have e0 : (if σ 0 = 2 then efx_three_bonus_distinct_values 2 0 else 0) = 18 := by
    rw [if_pos h]; rfl
  have e1 : (if σ 1 = 2 then efx_three_bonus_distinct_values 2 1 else 0) = 0 := by
    rw [if_neg h01]
  have e2 : (if σ 2 = 2 then efx_three_bonus_distinct_values 2 2 else 0) = 0 := by
    rw [if_neg h02]
  have e3 : (if σ 3 = 2 then efx_three_bonus_distinct_values 2 3 else 0) = 0 := by
    rw [if_neg h03]
  have e4 : (if σ 4 = 2 then efx_three_bonus_distinct_values 2 4 else 0) ≤ 17 := by
    split <;> simp [efx_three_bonus_distinct_values]
  have e5 : (if σ 5 = 2 then efx_three_bonus_distinct_values 2 5 else 0) ≤ 1 := by
    split <;> simp [efx_three_bonus_distinct_values]
  have e6 : (if σ 6 = 2 then efx_three_bonus_distinct_values 2 6 else 0) ≤ 1 := by
    split <;> simp [efx_three_bonus_distinct_values]
  have hsum : (∑ g, if σ g = 2 then efx_three_bonus_distinct_values 2 g else 0) ≤ 37 := by
    rw [Fin.sum_univ_seven, e0, e1, e2, e3]
    omega
  have := h3 2
  omega
