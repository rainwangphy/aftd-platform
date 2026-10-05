import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTau

/-!
# team_tau_le

Topic: algorithms   Node: aa10b0574ebd

The slack tau is at most 1/100.
-/

lemma team_tau_le (m : ℕ) : team_tau m ≤ 1 / 100 := by
  unfold team_tau
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith
