import AFTD.Prelude
import AFTD.Kb.Tcs.IsNormalizedRecurrence
import AFTD.Kb.Tcs.IsLogConcaveNewton
import AFTD.Kb.Tcs.RecurrenceProfile
import AFTD.Kb.Tcs.RecurrenceRatio
import AFTD.Kb.Tcs.HasPropertyP
import AFTD.Kb.Tcs.NewtonCoeff
import AFTD.Kb.Tcs.Op940Dim2PropertyPOfRatioCondition

/-!
# op_940_dim2_property_p_constant_ratio

Topic: combinatorics   Node: 7b0763deb3c1

Provenance: formalization of a published result. Source: arXiv:2611.01561 Thm 3.1

For N = 2 and any normalized recurrence coefficients a, b, c : Fin 3 → ℝ with log-concave Newton profile, if the ratio sequence is constant (r_1 = r_2), then property (P) holds.
-/

/-- Baseline property (P) for constant ratios in dimension N = 2. -/
theorem op_940_dim2_property_p_constant_ratio
    (a b c : Fin 3 → ℝ)
    (hrec : is_normalized_recurrence 2 a b c)
    (hlog : is_log_concave_newton 2 (recurrence_profile 2 b c))
    (hconst : recurrence_ratio 2 b c ⟨1, by decide⟩ = recurrence_ratio 2 b c ⟨2, by decide⟩) :
    has_property_p 2 a b c := by
  have hprof_0 : recurrence_profile 2 b c ⟨0, by decide⟩ = 0 := by
    rcases hrec with ⟨ha0, hb0, hc0, ha2, hsum, ha_pos, hc_pos, hb_nonneg⟩
    dsimp [recurrence_profile]
    change b ⟨0, Nat.zero_lt_succ 2⟩ + c ⟨0, Nat.zero_lt_succ 2⟩ = 0
    rw [hb0, hc0, add_zero]
  have hprof_2 : recurrence_profile 2 b c ⟨2, by decide⟩ = 1 := by
    rcases hrec with ⟨ha0, hb0, hc0, ha2, hsum, ha_pos, hc_pos, hb_nonneg⟩
    dsimp [recurrence_profile]
    change b ⟨2, Nat.lt_succ_self 2⟩ + c ⟨2, Nat.lt_succ_self 2⟩ = 1
    have hs := hsum ⟨2, Nat.lt_succ_self 2⟩
    rw [ha2] at hs
    linarith
  have hnewton : newton_coeff 2 (recurrence_profile 2 b c) 2 =
      recurrence_profile 2 b c ⟨0, by decide⟩ - 2 * recurrence_profile 2 b c ⟨1, by decide⟩ +
        recurrence_profile 2 b c ⟨2, by decide⟩ := by
    dsimp [newton_coeff]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp
    ring
  have hlog2 : 0 ≤ newton_coeff 2 (recurrence_profile 2 b c) 2 := by
    have h2 : (2 : ℕ) ∈ Finset.Icc 1 2 := by simp
    exact hlog.1 2 h2
  have hprof_1_le : recurrence_profile 2 b c ⟨1, by decide⟩ ≤ 1 / 2 := by
    rw [hnewton, hprof_0, hprof_2] at hlog2
    linarith
  set r1 := recurrence_ratio 2 b c ⟨1, by decide⟩
  set r2 := recurrence_ratio 2 b c ⟨2, by decide⟩
  set d1 := recurrence_profile 2 b c ⟨1, by decide⟩
  have hineq : d1 * (1 + r1 * r2) + r2 * (1 - r2) ≤ 1 := by
    have hr1 : r1 = r2 := hconst
    rw [hr1]
    have hid : 1 - (d1 * (1 + r2 * r2) + r2 * (1 - r2)) =
        (1/2 - d1) * (1 + r2 * r2) + (1/2) * (1 - r2)^2 := by ring
    have h1 : 0 ≤ (1/2 - d1) * (1 + r2 * r2) := by
      apply mul_nonneg
      · linarith
      · have : 1 + r2 * r2 = 1 + r2^2 := by ring
        rw [this]
        positivity
    have h2 : 0 ≤ (1/2 : ℝ) * (1 - r2)^2 := by positivity
    linarith
  exact op_940_dim2_property_p_of_ratio_condition a b c hrec hineq
