import AFTD.Prelude
import AFTD.Kb.Tcs.PellNumber

/-!
# pell_family_asymptotic_base

Topic: automata   Node: a6eca0a2532d

Provenance: formalization of a published result. Source: arXiv:2610.08525 Sec. 5, Theorem 14

The sequence (2 * pell_number (n - 2))^(1/n) converges to 1 + Real.sqrt 2 as n tends to infinity.
-/

/-- The sequence (2 * pell_number (n - 2))^(1/n) converges to 1 + √2 as n → ∞. -/
theorem pell_family_asymptotic_base :
    Filter.Tendsto (fun n : ℕ => ((2 * (pell_number (n - 2) : ℝ)) ^ ((1 : ℝ) / (n : ℝ))))
      Filter.atTop (nhds (1 + Real.sqrt 2)) := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_gt : (1:ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hsqrt2_lt : Real.sqrt 2 < 3/2 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 3/2)]; norm_num
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set b : ℝ := 1 - Real.sqrt 2 with hb_def
  set a : ℝ := 1 + Real.sqrt 2 with ha_def
  have a_pos : 0 < a := by rw [ha_def]; linarith
  have a_ge_one : 1 ≤ a := by rw [ha_def]; linarith
  have a_sq : a ^ 2 = 2 * a + 1 := by rw [ha_def]; nlinarith
  have b_sq : b ^ 2 = 2 * b + 1 := by rw [hb_def]; nlinarith
  have hb : |b| ≤ 1/2 := abs_le.2 ⟨by rw [hb_def]; linarith, by rw [hb_def]; linarith⟩
  have hsqrt2_ne : (2 * Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have closed_form : ∀ m : ℕ, (pell_number m : ℝ) = (a ^ m - b ^ m) / (2 * Real.sqrt 2) := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => simp [pell_number.eq_1]
    | one =>
      have h1 : a ^ 1 - b ^ 1 = 2 * Real.sqrt 2 := by
        rw [pow_one, pow_one, ha_def, hb_def]; ring
      rw [pell_number.eq_2, h1, div_self hsqrt2_ne]
      norm_num
    | more n ih1 ih2 =>
      have hstep : a ^ (n + 2) - b ^ (n + 2) = 2 * (a ^ (n + 1) - b ^ (n + 1)) + (a ^ n - b ^ n) := by
        rw [pow_add, pow_add, pow_add, pow_add, a_sq, b_sq]
        ring
      change ((pell_number (n + 2) : ℕ) : ℝ) = (a ^ (n + 2) - b ^ (n + 2)) / (2 * Real.sqrt 2)
      rw [show n + 2 = n.succ.succ from rfl, pell_number.eq_3, hstep]
      push_cast
      rw [ih1, ih2]
      ring
  have bounds : ∀ m : ℕ, 1 ≤ m →
      2 * (pell_number m : ℝ) ≤ 3 * a ^ m / (2 * Real.sqrt 2) ∧
      a ^ m / (2 * Real.sqrt 2) ≤ 2 * (pell_number m : ℝ) := by
    intro m hm
    have hkey : |b| ^ m ≤ (1/2) * a ^ m := by
      have h1 : |b| ^ m ≤ (1/2) ^ m := pow_le_pow_left₀ (abs_nonneg b) hb m
      have h2 : (1/2 : ℝ) ^ m ≤ (1/2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      rw [pow_one] at h2
      have h3 : (1 : ℝ) ≤ a ^ m := one_le_pow₀ a_ge_one
      have h4 : (1/2 : ℝ) * 1 ≤ (1/2) * a ^ m := by
        apply mul_le_mul_of_nonneg_left h3 (by norm_num)
      linarith
    have hbm : |b ^ m| ≤ (1/2) * a ^ m := by rw [abs_pow]; exact hkey
    have h1 : b ^ m ≤ (1/2) * a ^ m := le_trans (le_abs_self _) hbm
    have h2 : -(1/2) * a ^ m ≤ b ^ m := by
      have := neg_abs_le (b ^ m); linarith
    have hdu : a ^ m - b ^ m ≤ 3 * a ^ m / 2 := by linarith
    have hdl : a ^ m / 2 ≤ a ^ m - b ^ m := by linarith
    have e : (2:ℝ) * ((a ^ m - b ^ m) / (2 * Real.sqrt 2)) = (a ^ m - b ^ m) / Real.sqrt 2 := by
      field_simp
    constructor
    · rw [closed_form m, e, div_le_div_iff₀ hsqrt2_pos (by positivity)]
      nlinarith
    · rw [closed_form m, e, div_le_div_iff₀ (by positivity) hsqrt2_pos]
      nlinarith
  have hlim : ∀ c : ℝ, 0 < c → Filter.Tendsto (fun n : ℕ => c ^ ((1:ℝ)/(n:ℝ))) Filter.atTop (nhds 1) := by
    intro c hc
    have h1 : Filter.Tendsto (fun n : ℕ => Real.log c * (1/(n:ℝ))) Filter.atTop (nhds (Real.log c * 0)) :=
      Filter.Tendsto.const_mul (Real.log c) tendsto_one_div_atTop_nhds_zero_nat
    rw [mul_zero] at h1
    have h2 : Filter.Tendsto (fun n : ℕ => Real.exp (Real.log c * (1/(n:ℝ)))) Filter.atTop (nhds 1) := by
      have := Real.continuous_exp.continuousAt.tendsto.comp h1
      simpa [Function.comp_def] using this
    simpa only [Real.rpow_def_of_pos hc] using h2
  set c₁ : ℝ := 1 / (a ^ 2 * (2 * Real.sqrt 2)) with hc1_def
  set c₂ : ℝ := 3 / (a ^ 2 * (2 * Real.sqrt 2)) with hc2_def
  have hc1_pos : 0 < c₁ := by rw [hc1_def]; positivity
  have hc2_pos : 0 < c₂ := by rw [hc2_def]; positivity
  have step : ∀ n : ℕ, 3 ≤ n →
      a * c₁ ^ ((1:ℝ)/(n:ℝ)) ≤ ((2 * (pell_number (n-2) : ℝ)) ^ ((1:ℝ)/(n:ℝ)))
      ∧ ((2 * (pell_number (n-2) : ℝ)) ^ ((1:ℝ)/(n:ℝ))) ≤ a * c₂ ^ ((1:ℝ)/(n:ℝ)) := by
    intro n hn
    have hn3 : 1 ≤ n - 2 := by omega
    have hnn : n ≠ 0 := by omega
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnn
    have ha_rpow : (a ^ n : ℝ) ^ ((1:ℝ) / (n:ℝ)) = a := by
      rw [← Real.rpow_natCast a n, ← Real.rpow_mul a_pos.le]
      have he : (n:ℝ) * (1/(n:ℝ)) = 1 := by field_simp
      rw [he, Real.rpow_one]
    have hpow2 : a ^ (n - 2) = a ^ n / a ^ 2 := by
      have hpow : a ^ n = a ^ (n - 2) * a ^ 2 := by
        rw [← pow_add]; congr 1; omega
      rw [hpow]
      have : (a^2 : ℝ) ≠ 0 := by positivity
      field_simp
    have hbnd := bounds (n-2) hn3
    have hlo : a ^ n * c₁ ≤ 2 * (pell_number (n-2) : ℝ) := by
      have h := hbnd.2
      rw [hpow2] at h
      have he : a ^ n / a ^ 2 / (2 * Real.sqrt 2) = a ^ n * c₁ := by
        rw [hc1_def]; field_simp
      rwa [he] at h
    have hhi : 2 * (pell_number (n-2) : ℝ) ≤ a ^ n * c₂ := by
      have h := hbnd.1
      rw [hpow2] at h
      have he : 3 * (a ^ n / a ^ 2) / (2 * Real.sqrt 2) = a ^ n * c₂ := by
        rw [hc2_def]; field_simp
      rwa [he] at h
    have hA_nn : (0:ℝ) ≤ 2 * (pell_number (n-2) : ℝ) := by positivity
    have hexp_nn : (0:ℝ) ≤ 1/(n:ℝ) := by positivity
    constructor
    · have h1 := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ a ^ n * c₁) hlo hexp_nn
      rwa [Real.mul_rpow (pow_nonneg a_pos.le n) hc1_pos.le, ha_rpow] at h1
    · have h1 := Real.rpow_le_rpow hA_nn hhi hexp_nn
      rwa [Real.mul_rpow (pow_nonneg a_pos.le n) hc2_pos.le, ha_rpow] at h1
  have hlimlo : Filter.Tendsto (fun n : ℕ => a * c₁ ^ ((1:ℝ)/(n:ℝ))) Filter.atTop (nhds a) := by
    have h := (hlim c₁ hc1_pos).const_mul a
    simpa using h
  have hlimhi : Filter.Tendsto (fun n : ℕ => a * c₂ ^ ((1:ℝ)/(n:ℝ))) Filter.atTop (nhds a) := by
    have h := (hlim c₂ hc2_pos).const_mul a
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlimlo hlimhi ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    exact (step n hn).1
  · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    exact (step n hn).2
