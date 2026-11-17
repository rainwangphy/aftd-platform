import AFTD.Prelude

/-!
# op869_log_integer_budget_upper

Topic: online_algorithms   Node: b16bd3e9eb7a

Provenance: helper lemma. The integer schedule and logarithmic inversion related to arXiv:2610.41516 Section 2.3.

For C≥1 and m≥2, the natural logarithm of the integer schedule budget is at most (3+2C)m³ log m.
-/

lemma op869_nat_le_two_pow_tmp (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 1 ≤ 2^n := by exact Nat.one_le_pow n 2 (by decide)
    rw [pow_succ]
    omega

/-- Upper bound for the logarithm of the integer fold-schedule budget. -/
theorem op869_log_integer_budget_upper (C m : ℕ) (hC : 1 ≤ C) (hm : 2 ≤ m) :
    Real.log (((C * (m^m)^3 * 2^(C*(m+1)))^(m^2) : ℕ) : ℝ) ≤
      (3 + 2*(C : ℝ)) * (m : ℝ)^3 * Real.log (m : ℝ) := by
  have hC0 : 0 < C := by omega
  have hm0 : 0 < m := by omega
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hCr : (0 : ℝ) ≤ C := by positivity
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
  have hlog2le : Real.log 2 ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hmR
  have hc2 : (C : ℝ) ≤ (2 : ℝ)^C := by exact_mod_cast op869_nat_le_two_pow_tmp C
  have hlogC : Real.log (C : ℝ) ≤ (C : ℝ) * Real.log 2 := by
    calc
      Real.log (C : ℝ) ≤ Real.log ((2 : ℝ)^C) := Real.log_le_log (by positivity) hc2
      _ = (C : ℝ) * Real.log 2 := Real.log_pow _ _
  let F : ℕ := C * (m^m)^3 * 2^(C*(m+1))
  have hF0 : 0 < F := by dsimp [F]; positivity
  have hlogF : Real.log (F : ℝ) = Real.log (C : ℝ) + 3*(m : ℝ)*Real.log (m : ℝ) +
      (C : ℝ)*((m : ℝ)+1)*Real.log 2 := by
    dsimp [F]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hmul1 : 0 ≤ (C : ℝ) * (Real.log (m : ℝ) - Real.log 2) :=
    mul_nonneg hCr (sub_nonneg.mpr hlog2le)
  have hmul2 : 0 ≤ ((C : ℝ) * ((m : ℝ)+1)) * (Real.log (m : ℝ) - Real.log 2) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hlog2le)
  have hmul3 : 0 ≤ ((C : ℝ) * ((m : ℝ)-2)) * Real.log (m : ℝ) :=
    mul_nonneg (mul_nonneg hCr (by linarith)) hlogm
  have hupper : Real.log (F : ℝ) ≤ (3+2*(C : ℝ))*(m : ℝ)*Real.log (m : ℝ) := by
    rw [hlogF]
    nlinarith
  change Real.log ((F^(m^2) : ℕ) : ℝ) ≤ _
  push_cast
  rw [Real.log_pow]
  push_cast
  calc
    (m : ℝ)^2 * Real.log (F : ℝ) ≤ (m : ℝ)^2 * ((3+2*(C : ℝ))*(m : ℝ)*Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = (3+2*(C : ℝ))*(m : ℝ)^3*Real.log (m : ℝ) := by ring
