import AFTD.Prelude

/-!
# stake_share_best_response

Topic: mechanism_design   Node: 9067de09b357

Best-response bound for the stake-share mechanism: if (L - c + K M) R = K W^2, 0 <= R, 0 < W <= M and the equilibrium utility (W - R)/W (pool(W) - c) is at least L - c, then no stake t >= 0 against others' total R does better.
-/

lemma stake_share_best_response {L K M c R W t : ℝ} (hK : 0 < K) (hc : c ≤ L) (hR : 0 ≤ R)
    (hW : 0 < W) (hWM : W ≤ M) (hAR : (L - c + K * M) * R = K * W ^ 2)
    (hu : L - c ≤ (W - R) / W * (L + K * max 0 (M - W) - c)) (ht : 0 ≤ t) :
    t / (t + R) * (L + K * max 0 (M - (t + R)) - c) ≤
      (W - R) / W * (L + K * max 0 (M - W) - c) := by
  rcases ht.lt_or_eq with htpos | htzero
  · have hy : 0 < t + R := by linarith
    by_cases hyM : t + R ≤ M
    · rw [max_eq_right (sub_nonneg.2 hyM), max_eq_right (sub_nonneg.2 hWM), div_mul_eq_mul_div,
        div_mul_eq_mul_div, div_le_div_iff₀ hy hW]
      have key : (W - R) * (L + K * (M - W) - c) * (t + R) - t * (L + K * (M - (t + R)) - c) * W =
          K * W * (t + R - W) ^ 2 := by
        linear_combination (-(t + R - W)) * hAR
      have : 0 ≤ K * W * (t + R - W) ^ 2 := by positivity
      linarith
    · push Not at hyM
      rw [max_eq_left (by linarith : M - (t + R) ≤ 0), mul_zero, add_zero]
      have h1 : t / (t + R) ≤ 1 := (div_le_one hy).mpr (by linarith)
      have h2 : 0 ≤ t / (t + R) := div_nonneg htpos.le hy.le
      nlinarith
  · rw [← htzero, zero_div, zero_mul]
    linarith
