import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsExPostSafeProcurementFor
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAlloc
import AFTD.Kb.GameTheoryEconomics.ProportionalSharePay
import AFTD.Kb.GameTheoryEconomics.ProportionalShareUtilityEq
import AFTD.Kb.GameTheoryEconomics.StakeSharePool

/-!
# stake_share_ex_post_safe

Topic: mechanism_design   Node: de78e255122b

With K > 0 and M > 0, the stake-share mechanism is ex-post safe for every agent whose cost is at most L.
-/

theorem stake_share_ex_post_safe {L K M c : ℝ} (hK : 0 < K) (hM : 0 < M) (hc : c ≤ L) :
    is_ex_post_safe_procurement_for proportional_share_alloc
      (proportional_share_pay (stake_share_pool L K M)) c := by
  refine ⟨[M / 2], by simp; linarith, fun others hothers => ?_, [], by simp, ?_⟩
  · rw [proportional_share_utility_eq]
    have h1 : 0 ≤ others.sum := List.sum_nonneg hothers
    have h2 : c ≤ stake_share_pool L K M ([M / 2].sum + others.sum) := by
      unfold stake_share_pool
      have := le_max_left 0 (M - ([M / 2].sum + others.sum))
      nlinarith
    apply mul_nonneg
    · apply div_nonneg <;> simp <;> linarith
    · linarith
  · rw [proportional_share_utility_eq]
    simp only [List.sum_singleton, List.sum_nil, add_zero]
    rw [div_self (by linarith), one_mul]
    unfold stake_share_pool
    rw [max_eq_right (by linarith)]
    nlinarith
