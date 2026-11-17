import AFTD.Prelude

/-!
# op869_integer_schedule_asymptotic

Topic: online_algorithms   Node: a883291c927f

Provenance: helper lemma. The schedule inversion is related to arXiv:2610.41516 Section 2.3; this uses the explicit m^m and F^(m²) schedule.

For every positive integer C, the integer budget F_m^(m²) fits in any sufficiently large n for some m≥2 whose target m^m is at least exp(c(log n)^(1/3)(log log n)^(2/3)), with a positive constant c depending only on C.
-/

def op869_asym_integer_budget_internal (C m : ℕ) : ℕ :=
  (C*(m^m)^3*2^(C*(m+1)))^(m^2)

theorem op869_asym_budget_big_internal (C m : ℕ) (hC : 1 ≤ C) (hm : 1 ≤ m) :
    m ≤ op869_asym_integer_budget_internal C m := by
  have hm0 : 0 < m := by omega
  let K := m^m
  let F := C*K^3*2^(C*(m+1))
  have hK : m ≤ K := by dsimp [K]; exact Nat.le_pow hm0
  have hKpow : K ≤ K^3 := Nat.le_pow (by decide)
  have hF : K^3 ≤ F := by
    dsimp [F]
    have hp : 1 ≤ 2^(C*(m+1)) := Nat.one_le_pow _ _ (by decide)
    calc
      K^3 = 1*K^3*1 := by simp
      _ ≤ C*K^3*2^(C*(m+1)) := by gcongr
  have hm2 : 0 < m^2 := by positivity
  have hpow : F ≤ F^(m^2) := Nat.le_pow hm2
  exact le_trans hK (le_trans hKpow (le_trans hF hpow))

theorem op869_asym_maximal_budget_internal (B : ℕ → ℕ) (hbig : ∀ m, 1 ≤ m → m ≤ B m) (n : ℕ) (h2 : B 2 ≤ n) :
    ∃ m, 2 ≤ m ∧ B m ≤ n ∧ n < B (m+1) := by
  classical
  have hn2 : 2 ≤ n := le_trans (hbig 2 (by decide)) h2
  let p : ℕ → Prop := fun m => B m ≤ n
  let m := Nat.findGreatest p (n+1)
  have hm2 : 2 ≤ m := Nat.le_findGreatest (by omega : 2 ≤ n+1) h2
  have hm : B m ≤ n := by
    change p m
    exact Nat.findGreatest_spec (P := p) (by omega : 2 ≤ n+1) h2
  have hmn : m ≤ n := le_trans (hbig m (by omega)) hm
  have hnot : ¬ B (m+1) ≤ n := by
    change ¬ p (m+1)
    exact Nat.findGreatest_is_greatest (P := p) (by omega : m < m+1) (by omega : m+1 ≤ n+1)
  exact ⟨m, hm2, hm, by omega⟩

lemma op869_asym_nat_le_two_pow_internal (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 1 ≤ 2^n := by exact Nat.one_le_pow n 2 (by decide)
    rw [pow_succ]
    omega

theorem op869_asym_log_upper_internal (C m : ℕ) (hC : 1 ≤ C) (hm : 2 ≤ m) :
    Real.log (((C * (m^m)^3 * 2^(C*(m+1)))^(m^2) : ℕ) : ℝ) ≤
      (3 + 2*(C : ℝ)) * (m : ℝ)^3 * Real.log (m : ℝ) := by
  have hC0 : 0 < C := by omega
  have hm0 : 0 < m := by omega
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hCr : (0 : ℝ) ≤ C := by positivity
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
  have hlog2le : Real.log 2 ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hmR
  have hc2 : (C : ℝ) ≤ (2 : ℝ)^C := by exact_mod_cast op869_asym_nat_le_two_pow_internal C
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

theorem op869_asym_log_succ_internal (C m : ℕ) (hC : 1 ≤ C) (hm : 2 ≤ m) :
    Real.log (((C * ((m+1)^(m+1))^3 * 2^(C*((m+1)+1)))^((m+1)^2) : ℕ) : ℝ) ≤
      16*(3+2*(C : ℝ))*(m : ℝ)^3*Real.log (m : ℝ) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
  have hmplus : (m : ℝ)+1 ≤ (m : ℝ)^2 := by nlinarith
  have hlogplus : Real.log ((m : ℝ)+1) ≤ 2*Real.log (m : ℝ) := by
    calc
      Real.log ((m : ℝ)+1) ≤ Real.log ((m : ℝ)^2) := Real.log_le_log (by positivity) hmplus
      _ = 2*Real.log (m : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogplus0 : 0 ≤ Real.log ((m : ℝ)+1) := Real.log_nonneg (by linarith)
  have hpow : ((m : ℝ)+1)^3 ≤ (2*(m : ℝ))^3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hprod : ((m : ℝ)+1)^3*Real.log ((m : ℝ)+1) ≤
      (2*(m : ℝ))^3*(2*Real.log (m : ℝ)) := by
    gcongr
  have hA : 0 ≤ 3+2*(C : ℝ) := by positivity
  have h := op869_asym_log_upper_internal C (m+1) hC (by omega)
  calc
    Real.log (((C * ((m+1)^(m+1))^3 * 2^(C*((m+1)+1)))^((m+1)^2) : ℕ) : ℝ) ≤
        (3+2*(C : ℝ))*(((m : ℝ)+1)^3*Real.log ((m : ℝ)+1)) := by simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using h
    _ ≤ (3+2*(C : ℝ))*((2*(m : ℝ))^3*(2*Real.log (m : ℝ))) :=
      mul_le_mul_of_nonneg_left hprod hA
    _ = 16*(3+2*(C : ℝ))*(m : ℝ)^3*Real.log (m : ℝ) := by ring

theorem op869_asym_loglog_internal (x m D : ℝ) (hx : 0 < x) (hm : 2 ≤ m) (hD : 1 ≤ D)
    (hbound : x ≤ D*m^3*Real.log m) :
    Real.log x ≤ (4+D/Real.log 2)*Real.log m := by
  have hm0 : 0 < m := by linarith
  have hD0 : 0 < D := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hlogle : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm
  have hlogD : Real.log D ≤ D := by
    have h := Real.log_le_sub_one_of_pos hD0
    linarith
  have hloglog : Real.log (Real.log m) ≤ Real.log m := by
    have h := Real.log_le_sub_one_of_pos hlogm
    linarith
  have hratio : D ≤ (D / Real.log 2) * Real.log m := by
    calc
      D = (D / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ (D / Real.log 2) * Real.log m :=
        mul_le_mul_of_nonneg_left hlogle (div_nonneg (by linarith) hlog2.le)
  have hlogbound : Real.log x ≤ Real.log (D*m^3*Real.log m) :=
    Real.log_le_log hx hbound
  have hlogeq : Real.log (D*m^3*Real.log m) =
      Real.log D + 3*Real.log m + Real.log (Real.log m) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow]
    norm_num
  rw [hlogeq] at hlogbound
  nlinarith

theorem op869_asym_scalar_inv_internal (x y m l A B : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hm : 0 ≤ m) (hl : 0 ≤ l) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hxbound : x ≤ A*m^3*l) (hybound : y ≤ B*l) :
    x^((1 : ℝ)/3) * y^((2 : ℝ)/3) ≤ (A*B^2+1)*m*l := by
  let z := x^((1 : ℝ)/3) * y^((2 : ℝ)/3)
  let u := m*l
  let D := A*B^2+1
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hu : 0 ≤ u := mul_nonneg hm hl
  have hD1 : 1 ≤ D := by
    have hnonneg : 0 ≤ A*B^2 := mul_nonneg hA (sq_nonneg B)
    dsimp [D]
    linarith
  have hD0 : 0 ≤ D := by linarith
  have hBbound : 0 ≤ B*l := mul_nonneg hB hl
  have hy2 : y^2 ≤ (B*l)^2 := pow_le_pow_left₀ hy hybound 2
  have hxy : x*y^2 ≤ (A*B^2)*u^3 := by
    calc
      x*y^2 ≤ (A*m^3*l) * (B*l)^2 := mul_le_mul hxbound hy2 (sq_nonneg y) (by positivity)
      _ = (A*B^2)*u^3 := by dsimp [u]; ring
  have hz3 : z^3 = x*y^2 := by
    dsimp [z]
    rw [mul_pow, ← Real.rpow_mul_natCast hx, ← Real.rpow_mul_natCast hy]
    norm_num [Real.rpow_natCast]
  have hDpow : D ≤ D^3 := by
    have hD2 : 1 ≤ D^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hD2 hD0
    nlinarith
  have hcoef : A*B^2 ≤ D^3 := by dsimp [D] at *; nlinarith
  have hcube : z^3 ≤ (D*u)^3 := by
    rw [hz3]
    calc
      x*y^2 ≤ (A*B^2)*u^3 := hxy
      _ ≤ D^3*u^3 := mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = (D*u)^3 := by ring
  have hfinal : z ≤ D*u := le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (mul_nonneg hD0 hu) hcube
  simpa [z, D, u, mul_assoc] using hfinal

/-- Invert the explicit integer fold-schedule budget. -/
theorem op869_integer_schedule_asymptotic (C : ℕ) (hC : 1 ≤ C) : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ m : ℕ, 2 ≤ m ∧ (let K := m^m; let F := C*K^3*2^(C*(m+1)); F^(m^2) ≤ n) ∧ Real.exp (c * (Real.log (n : ℝ) ^ ((1 : ℝ) / 3)) * (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3))) ≤ (m^m : ℝ) := by
  let D : ℝ := 16*(3+2*(C : ℝ))
  let E : ℝ := 4+D/Real.log 2
  let W : ℝ := D*E^2+1
  have hC0 : 0 ≤ (C : ℝ) := by positivity
  have hD1 : 1 ≤ D := by dsimp [D]; nlinarith
  have hD0 : 0 ≤ D := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE0 : 0 ≤ E := by
    dsimp [E]
    have h := div_nonneg hD0 hlog2.le
    linarith
  have hW0 : 0 < W := by
    dsimp [W]
    have h := mul_nonneg hD0 (sq_nonneg E)
    linarith
  refine ⟨1/W, by positivity, max 3 (op869_asym_integer_budget_internal C 2), ?_⟩
  intro n hn
  have hn3 : 3 ≤ n := le_trans (le_max_left _ _) hn
  have hnB : op869_asym_integer_budget_internal C 2 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨m, hm, hbudget, hnext⟩ := op869_asym_maximal_budget_internal (op869_asym_integer_budget_internal C)
    (fun j hj => op869_asym_budget_big_internal C j hC hj) n hnB
  refine ⟨m, hm, ?_, ?_⟩
  · simpa [op869_asym_integer_budget_internal] using hbudget
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn3r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hx1 : 1 ≤ Real.log (n : ℝ) :=
    (Real.le_log_iff_exp_le hn0).2 (le_trans Real.exp_one_lt_three.le hn3r)
  have hx0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hy0 : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg hx1
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hm2r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hl0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
  have hcast : (n : ℝ) ≤ (op869_asym_integer_budget_internal C (m+1) : ℕ) := by exact_mod_cast (Nat.le_of_lt hnext)
  have hlogn : Real.log (n : ℝ) ≤ Real.log (op869_asym_integer_budget_internal C (m+1) : ℕ) :=
    Real.log_le_log hn0 hcast
  have hsucc := op869_asym_log_succ_internal C m hC hm
  change Real.log (op869_asym_integer_budget_internal C (m+1) : ℕ) ≤
    D*(m : ℝ)^3*Real.log (m : ℝ) at hsucc
  have hxbound : Real.log (n : ℝ) ≤ D*(m : ℝ)^3*Real.log (m : ℝ) := le_trans hlogn hsucc
  have hybound : Real.log (Real.log (n : ℝ)) ≤ E*Real.log (m : ℝ) := by
    have h := op869_asym_loglog_internal (Real.log (n : ℝ)) (m : ℝ) D (by linarith) hm2r hD1 hxbound
    simpa [E] using h
  have hscalar := op869_asym_scalar_inv_internal (Real.log (n : ℝ)) (Real.log (Real.log (n : ℝ)))
    (m : ℝ) (Real.log (m : ℝ)) D E hx0 hy0 hm0 hl0 hD0 hE0 hxbound hybound
  have hscale : (1/W) * (Real.log (n : ℝ) ^ ((1 : ℝ)/3)) *
      (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ)/3)) ≤ (m : ℝ)*Real.log (m : ℝ) := by
    calc
      (1/W) * (Real.log (n : ℝ) ^ ((1 : ℝ)/3)) *
          (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ)/3)) =
          ((Real.log (n : ℝ) ^ ((1 : ℝ)/3)) *
          (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ)/3))) / W := by ring
      _ ≤ (m : ℝ)*Real.log (m : ℝ) := by
        apply (div_le_iff₀ hW0).2
        simpa only [W, mul_assoc, mul_comm, mul_left_comm] using hscalar
  calc
    Real.exp ((1/W) * (Real.log (n : ℝ) ^ ((1 : ℝ)/3)) *
        (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ)/3))) ≤
        Real.exp ((m : ℝ)*Real.log (m : ℝ)) := Real.exp_le_exp.mpr hscale
    _ = Real.exp (Real.log ((m : ℝ)^m)) := by rw [Real.log_pow]
    _ = (m^m : ℝ) := Real.exp_log (by positivity)
