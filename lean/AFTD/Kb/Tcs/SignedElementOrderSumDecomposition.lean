import AFTD.Prelude
import AFTD.Kb.Tcs.PermSignedOrderSum
import AFTD.Kb.Tcs.PermSignedLcmTwoOrderSum
import AFTD.Kb.Tcs.PermOddOrderSum
import AFTD.Kb.Tcs.PermSignedLcmTwoSubOrder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# signed_element_order_sum_decomposition

Topic: combinatorics   Node: 426918f09531

Provenance: formalization of a published result. Source: arXiv:2611.29409 Lemma 3.1

For any natural number n, the signed element order sum D_n = ∑_{σ ∈ S_n} sgn(σ) o(σ) (`perm_signed_order_sum n : ℤ`) decomposes as D_n = D_n^* - V_n in ℤ, where D_n^* = ∑_{σ ∈ S_n} sgn(σ) lcm(2, o(σ)) (`perm_signed_lcm_two_order_sum n : ℤ`) and V_n = ∑_{σ ∈ S_n, o(σ) odd} o(σ) (`perm_odd_order_sum n : ℤ`).
-/

/-- Decomposition of the signed element order sum D_n as D_n* - V_n (arXiv:2611.29409 Lemma 3.1). -/
theorem signed_element_order_sum_decomposition (n : ℕ) : perm_signed_order_sum n = perm_signed_lcm_two_order_sum n - perm_odd_order_sum n := by
  have hdiff : perm_signed_lcm_two_order_sum n - perm_signed_order_sum n = perm_odd_order_sum n := by
    unfold perm_signed_lcm_two_order_sum perm_signed_order_sum perm_odd_order_sum
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro σ _
    exact perm_signed_lcm_two_sub_order σ
  linarith
