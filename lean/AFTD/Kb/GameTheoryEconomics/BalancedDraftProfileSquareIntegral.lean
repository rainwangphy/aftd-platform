import AFTD.Prelude

/-!
# balanced_draft_profile_square_integral

Topic: fair_division   Node: ecd5e4691da0

Provenance: helper lemma. Variance calculation in the one-agent limit of OP-1493.

For n at least two, the integral over [0,1] of the squared limiting threshold profile (1-x)^(2/n) is n/(n+2).
-/

open MeasureTheory intervalIntegral

theorem balanced_draft_profile_square_integral (n : ℕ) (hn : 2 ≤ n) :
    (∫ x : ℝ in (0:ℝ)..1, (1-x) ^ ((2:ℝ)/(n:ℝ))) = (n:ℝ)/((n:ℝ)+2) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hr : -1 < (2:ℝ)/(n:ℝ) := by
    have h : 0 ≤ (2:ℝ)/(n:ℝ) := by positivity
    linarith
  have hplus : (2:ℝ)/(n:ℝ) + 1 ≠ 0 := by linarith
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ ((2:ℝ)/(n:ℝ))) 1]
  norm_num only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl hr)]
  have hpow : (0:ℝ) ^ ((2:ℝ)/(n:ℝ)+1) = 0 := by
    apply Real.zero_rpow
    linarith
  rw [hpow, Real.one_rpow]
  field_simp
  ring
