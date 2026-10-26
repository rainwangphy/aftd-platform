import AFTD.Prelude
import AFTD.Kb.Tcs.NonclairvoyantSchedulingOfflineOpt
import AFTD.Kb.Tcs.NonclairvoyantSchedulingOfflineOptSuperadditive
import AFTD.Kb.Tcs.RatioAddLeMaxOfNonneg

/-!
# nonclairvoyant_scheduling_round_robin_hybrid_competitive_ratio

Topic: online_algorithms   Node: 9439ce7fbfca

Provenance: formalization of a published result. Source: arXiv:2610.29037 Lemma 4.2

Let n be a natural number and let x, a, z : Fin n → ℝ with x = a + z, where a and z have non-negative coordinates (∀ i, 0 ≤ a i and ∀ i, 0 ≤ z i). Suppose an algorithm accumulates non-negative cost C_T ≥ 0 by time T and incurs total completion cost alg_cost ≤ C_T + (2 * n / (n + 1)) * nonclairvoyant_scheduling_offline_opt z by running Round-Robin after time T. If nonclairvoyant_scheduling_offline_opt a > 0, then the competitive ratio satisfies alg_cost / nonclairvoyant_scheduling_offline_opt x ≤ max (C_T / nonclairvoyant_scheduling_offline_opt a) (2 * (n : ℝ) / ((n : ℝ) + 1)).
-/

lemma nonclairvoyant_scheduling_round_robin_hybrid_competitive_ratio_opt_nonneg
    {n : ℕ} (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ nonclairvoyant_scheduling_offline_opt z := by
  unfold nonclairvoyant_scheduling_offline_opt
  refine Finset.le_inf' _ _ (fun π _ => ?_)
  refine Finset.sum_nonneg (fun i _ => ?_)
  have hi : (i : ℝ) ≤ (n : ℝ) := by
    exact le_of_lt (Nat.cast_lt.mpr i.isLt)
  have h_diff : 0 ≤ (n : ℝ) - (i : ℝ) := sub_nonneg.mpr hi
  exact mul_nonneg h_diff (hz (π i))

/-- Robustness reduction to error-detection time for Round-Robin hybrid schedules. -/
theorem nonclairvoyant_scheduling_round_robin_hybrid_competitive_ratio
    {n : ℕ} (x a z : Fin n → ℝ)
    (hxz : x = a + z)
    (ha : ∀ i, 0 ≤ a i)
    (hz : ∀ i, 0 ≤ z i)
    (C_T : ℝ) (hC_T : 0 ≤ C_T) (alg_cost : ℝ)
    (h_alg : alg_cost ≤ C_T + (2 * (n : ℝ) / ((n : ℝ) + 1)) * nonclairvoyant_scheduling_offline_opt z)
    (h_opt_a : 0 < nonclairvoyant_scheduling_offline_opt a) :
    alg_cost / nonclairvoyant_scheduling_offline_opt x ≤
      max (C_T / nonclairvoyant_scheduling_offline_opt a) (2 * (n : ℝ) / ((n : ℝ) + 1)) := by
  set rho := 2 * (n : ℝ) / ((n : ℝ) + 1)
  have hz_nonneg : 0 ≤ nonclairvoyant_scheduling_offline_opt z :=
    nonclairvoyant_scheduling_round_robin_hybrid_competitive_ratio_opt_nonneg z hz
  have h_super : nonclairvoyant_scheduling_offline_opt a + nonclairvoyant_scheduling_offline_opt z ≤
      nonclairvoyant_scheduling_offline_opt x := by
    have hs := nonclairvoyant_scheduling_offline_opt_superadditive a z
    rw [hxz]
    exact hs
  have h_rho_nonneg : 0 ≤ rho := by
    dsimp [rho]
    refine div_nonneg ?_ ?_
    · positivity
    · positivity
  have hc_nonneg : 0 ≤ C_T + rho * nonclairvoyant_scheduling_offline_opt z := by
    refine add_nonneg hC_T (mul_nonneg h_rho_nonneg hz_nonneg)
  have hd_pos : 0 < nonclairvoyant_scheduling_offline_opt a + nonclairvoyant_scheduling_offline_opt z :=
    add_pos_of_pos_of_nonneg h_opt_a hz_nonneg
  have h_div : alg_cost / nonclairvoyant_scheduling_offline_opt x ≤
      (C_T + rho * nonclairvoyant_scheduling_offline_opt z) /
        (nonclairvoyant_scheduling_offline_opt a + nonclairvoyant_scheduling_offline_opt z) :=
    div_le_div₀ hc_nonneg h_alg hd_pos h_super
  have h_ratio := ratio_add_le_max_of_nonneg C_T (nonclairvoyant_scheduling_offline_opt a)
    (nonclairvoyant_scheduling_offline_opt z) rho h_opt_a hz_nonneg
  exact le_trans h_div h_ratio
