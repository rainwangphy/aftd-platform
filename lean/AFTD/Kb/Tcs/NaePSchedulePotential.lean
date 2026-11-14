import AFTD.Prelude
import AFTD.Kb.Tcs.NaePSchedule
import AFTD.Kb.Tcs.NaeAngleContraction
import AFTD.Kb.Tcs.NaeArccosCosLe

/-!
# nae_p_schedule_potential

Topic: quantum   Node: a7d655a730a9

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For every triple (d, θ, q) reachable by the specified p-computation rule schedule, 0 ≤ θ ≤ π, q ≥ 0, and θ ≤ πq(15/32)^d.
-/

theorem nae_p_schedule_potential {d : ℕ} {θ q : ℝ} (h : nae_p_schedule d θ q) :
    0 ≤ θ ∧ θ ≤ Real.pi ∧ 0 ≤ q ∧
      θ ≤ Real.pi * q * (15 / 32 : ℝ) ^ d := by
  induction h with
  | initial =>
      simp [Real.pi_pos.le]
  | @compose d θ q h ih =>
      rcases ih with ⟨ht0, htpi, hq0, hpot⟩
      refine ⟨Real.arccos_nonneg _, Real.arccos_le_pi _, by positivity, ?_⟩
      have hc := nae_angle_contraction θ ht0 htpi
      have hm := mul_le_mul_of_nonneg_left hpot (show (0 : ℝ) ≤ 15 / 16 by norm_num)
      have hid : Real.pi * (2 * q) * (15 / 32 : ℝ) ^ (d + 1) =
          (15 / 16 : ℝ) * (Real.pi * q * (15 / 32 : ℝ) ^ d) := by
        rw [pow_succ]
        ring
      rw [hid]
      exact le_trans hc hm
  | @amplify d θ q c hc h ih =>
      rcases ih with ⟨ht0, htpi, hq0, hpot⟩
      have hc0 : (0 : ℝ) ≤ c := by positivity
      refine ⟨Real.arccos_nonneg _, Real.arccos_le_pi _, by positivity, ?_⟩
      have ha := nae_arccos_cos_le ((c : ℝ) * θ) (mul_nonneg hc0 ht0)
      have hm := mul_le_mul_of_nonneg_left hpot hc0
      nlinarith
  | @relax d θ q θ' hθ'0 hθ'le h ih =>
      rcases ih with ⟨ht0, htpi, hq0, hpot⟩
      exact ⟨hθ'0, le_trans hθ'le htpi, hq0, le_trans hθ'le hpot⟩
