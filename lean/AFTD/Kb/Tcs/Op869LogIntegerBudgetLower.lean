import AFTD.Prelude

/-!
# op869_log_integer_budget_lower

Topic: online_algorithms   Node: 9fdbb0ca7b8d

Provenance: helper lemma. The explicit integer schedule related to arXiv:2610.41516 Section 2.3.

For C≥1 and m≥2, the logarithm of the integer schedule budget is at least 3m³ log m.
-/

/-- Lower bound for the logarithm of the integer fold-schedule budget. -/
theorem op869_log_integer_budget_lower (C m : ℕ) (hC : 1 ≤ C) (hm : 2 ≤ m) :
    3 * (m : ℝ)^3 * Real.log (m : ℝ) ≤
      Real.log (((C * (m^m)^3 * 2^(C*(m+1)))^(m^2) : ℕ) : ℝ) := by
  have hm0 : 0 < m := by omega
  have hC0 : 0 < C := by omega
  let K := m^m
  let F := C*K^3*2^(C*(m+1))
  have hK0 : 0 < K := by dsimp [K]; positivity
  have hFbound : K^3 ≤ F := by
    dsimp [F]
    have hp : 1 ≤ 2^(C*(m+1)) := Nat.one_le_pow _ _ (by decide)
    calc
      K^3 = 1*K^3*1 := by simp
      _ ≤ C*K^3*2^(C*(m+1)) := by gcongr
  have hcast : ((K^3 : ℕ) : ℝ) ≤ (F : ℝ) := by exact_mod_cast hFbound
  have hlog : Real.log (((K^3 : ℕ) : ℝ)) ≤ Real.log (F : ℝ) :=
    Real.log_le_log (by positivity) hcast
  have hlogK : 3*(m : ℝ)*Real.log (m : ℝ) ≤ Real.log (F : ℝ) := by
    simpa [K, Nat.cast_pow, Real.log_pow, mul_assoc] using hlog
  change _ ≤ Real.log ((F^(m^2) : ℕ) : ℝ)
  push_cast
  rw [Real.log_pow]
  push_cast
  calc
    3 * (m : ℝ)^3 * Real.log (m : ℝ) = (m : ℝ)^2 * (3*(m : ℝ)*Real.log (m : ℝ)) := by ring
    _ ≤ (m : ℝ)^2 * Real.log (F : ℝ) := mul_le_mul_of_nonneg_left hlogK (by positivity)
