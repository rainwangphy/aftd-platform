import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsProcurementPne
import AFTD.Kb.GameTheoryEconomics.ProcurementOthersBidsSum
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAlloc
import AFTD.Kb.GameTheoryEconomics.ProportionalSharePay
import AFTD.Kb.GameTheoryEconomics.ProportionalShareUtilityEq
import AFTD.Kb.GameTheoryEconomics.StakeShareDeviationLe
import AFTD.Kb.GameTheoryEconomics.StakeSharePool

/-!
# stake_share_two_agent_pne

Topic: mechanism_design   Node: dcf8c85319d9

With pool 1 + max(0, 2 - W) and costs 1/5 and 9/10, the stakes 24/35 and 18/35 form a pure Nash equilibrium.
-/

/-- Two agents with costs `1/5` and `9/10`, stake-share pool `1 + max 0 (2 - W)`: the stakes `24/35` and `18/35` form a pure Nash equilibrium, splitting the work `4/7` and `3/7`. -/
theorem stake_share_two_agent_pne :
    is_procurement_pne proportional_share_alloc
      (proportional_share_pay (stake_share_pool 1 1 2)) ![1/5, 9/10] ![[24/35], [18/35]] := by
  refine ⟨fun i b hb => ?_, fun i σ hσ => ?_⟩
  · fin_cases i <;> simp at hb <;> rw [hb] <;> norm_num
  · have hσs : 0 ≤ σ.sum := List.sum_nonneg hσ
    rw [proportional_share_utility_eq, proportional_share_utility_eq,
      procurement_others_bids_sum]
    fin_cases i
    · simp only [Fin.sum_univ_two, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, List.sum_singleton]
      norm_num
      unfold stake_share_pool
      norm_num
      apply stake_share_deviation_le (by norm_num) hσs (by norm_num) (by norm_num)
      intro _; nlinarith [sq_nonneg (σ.sum - 24/35)]
    · simp only [Fin.sum_univ_two, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, List.sum_singleton]
      norm_num
      unfold stake_share_pool
      norm_num
      apply stake_share_deviation_le (by norm_num) hσs (by norm_num) (by norm_num)
      intro _; nlinarith [sq_nonneg (σ.sum - 18/35)]
