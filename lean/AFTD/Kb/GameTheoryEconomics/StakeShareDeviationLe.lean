import AFTD.Prelude

/-!
# stake_share_deviation_le

Topic: mechanism_design   Node: b31006bda09c

A bound used for the two-agent equilibrium: with pool 1 + max(0, 2 - W), a stake s against others' total R yields utility at most u0 when the quadratic condition holds below W = 2 and 1 - c <= u0.
-/

lemma stake_share_deviation_le {R c u0 s : ℝ} (hR : 0 < R) (hs : 0 ≤ s) (hc : c ≤ 1)
    (hfar : 1 - c ≤ u0)
    (hquad : s + R ≤ 2 → s * (3 - c - (s + R)) ≤ u0 * (s + R)) :
    s / (s + R) * (1 + max 0 (2 - (s + R)) - c) ≤ u0 := by
  have hW : 0 < s + R := by linarith
  rcases le_or_gt (s + R) 2 with h | h
  · rw [max_eq_right (by linarith), div_mul_eq_mul_div, div_le_iff₀ hW]
    have := hquad h
    nlinarith
  · rw [max_eq_left (by linarith)]
    have h1 : s / (s + R) ≤ 1 := (div_le_one hW).mpr (by linarith)
    have h2 : 0 ≤ s / (s + R) := div_nonneg hs hW.le
    nlinarith
