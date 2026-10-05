import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTau

/-!
# team_tau_mul_le

Topic: algorithms   Node: bb9ae74bf70c

2 tau m is at most 1/50.
-/

lemma team_tau_mul_le (m : ℕ) : 2 * team_tau m * m ≤ 1 / 50 := by
  unfold team_tau
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [show 2 * (1 / (100 * ((m : ℝ) + 1))) * m = m / (50 * ((m : ℝ) + 1)) by field_simp; ring]
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith
