import AFTD.Prelude

/-!
# op_902_tail_bound_implies_poly_bound

Topic: online_algorithms   Node: 6fb5541e400b

Provenance: helper lemma. step towards op_902_poly_time_carpooling_cube_root_log_discrepancy

There exist positive real constants C and c such that for every natural number T ≥ 2, the threshold D = ceil(C * (log T)^(1/3)) satisfies 300 ≤ D and the exponential tail bound 12 * T * exp(-(D/40)^3) is at most T^(-c).
-/

/-- Real-analytic bound converting the continuous tail bound 12 * T * exp(-(D/40)^3) at threshold D = ceil(C * (log T)^(1/3)) to a polynomial probability bound T^(-c). -/
theorem op_902_tail_bound_implies_poly_bound :
    ∃ (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ (T : ℕ) (hT : 2 ≤ T),
        let D := Nat.ceil (C * (Real.log (T : ℝ)) ^ ((1 : ℝ) / 3))
        300 ≤ D ∧ 12 * (T : ℝ) * Real.exp (-(((D : ℝ) / 40) ^ 3)) ≤ (T : ℝ) ^ (-c) := by
  refine ⟨400, 1, by norm_num, by norm_num, ?_⟩
  intro T hT
  dsimp only
  have hTreal : (2:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  have hTpos : (0:ℝ) < (T:ℝ) := by linarith
  have hlog2le : Real.log (2:ℝ) ≤ Real.log (T:ℝ) :=
    Real.log_le_log (by norm_num) hTreal
  have hlog2gt : (27/64:ℝ) < Real.log (2:ℝ) := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hcube : (3/4:ℝ)^3 < Real.log (T:ℝ) := by
    have h1 : (27/64:ℝ) < Real.log (T:ℝ) := lt_of_lt_of_le hlog2gt hlog2le
    norm_num at h1 ⊢
    exact h1
  have hleft : (((3/4:ℝ)^3) ^ ((1:ℝ)/3)) = 3/4 := by
    rw [← Real.rpow_natCast (3/4) 3]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3/4)]
    norm_num
  have hroot_gt : (3/4:ℝ) < (Real.log (T:ℝ)) ^ ((1:ℝ)/3) := by
    have hrpow : (((3/4:ℝ)^3) ^ ((1:ℝ)/3)) < (Real.log (T:ℝ)) ^ ((1:ℝ)/3) :=
      Real.rpow_lt_rpow (by positivity) hcube (by norm_num)
    calc
      (3/4:ℝ) = (((3/4:ℝ)^3) ^ ((1:ℝ)/3)) := hleft.symm
      _ < (Real.log (T:ℝ)) ^ ((1:ℝ)/3) := hrpow
  let D : ℕ := Nat.ceil (400 * (Real.log (T:ℝ)) ^ ((1:ℝ)/3))
  have hx_gt : (300:ℝ) < 400 * (Real.log (T:ℝ)) ^ ((1:ℝ)/3) := by
    nlinarith [hroot_gt]
  have hx_le_D : 400 * (Real.log (T:ℝ)) ^ ((1:ℝ)/3) ≤ (D:ℝ) := Nat.le_ceil _
  have hD_ge_300 : 300 ≤ D := by
    have h : (300:ℝ) ≤ (D:ℝ) := le_of_lt (lt_of_lt_of_le hx_gt hx_le_D)
    exact_mod_cast h
  change 300 ≤ D ∧ 12 * (T:ℝ) * Real.exp (-(((D:ℝ)/40)^3)) ≤ (T:ℝ)^(-1:ℝ)
  constructor
  · exact hD_ge_300
  · have hlogT_nonneg : 0 ≤ Real.log (T:ℝ) := by
      have hpos : (0:ℝ) < Real.log (2:ℝ) := by
        linarith [hlog2gt]
      linarith
    have hr_nonneg : 0 ≤ (Real.log (T:ℝ)) ^ ((1:ℝ)/3) :=
      Real.rpow_nonneg hlogT_nonneg _
    have hr_cube : ((Real.log (T:ℝ)) ^ ((1:ℝ)/3))^3 = Real.log (T:ℝ) := by
      rw [show ((1:ℝ)/3) = ((3:ℕ):ℝ)⁻¹ by norm_num]
      apply Real.rpow_inv_natCast_pow
      · exact hlogT_nonneg
      · norm_num
    have hD_div : (10:ℝ) * ((Real.log (T:ℝ)) ^ ((1:ℝ)/3)) ≤ (D:ℝ)/40 := by
      nlinarith
    have hcubeD : 1000 * Real.log (T:ℝ) ≤ ((D:ℝ)/40)^3 := by
      have hmono : (10 * ((Real.log (T:ℝ)) ^ ((1:ℝ)/3)))^3 ≤ ((D:ℝ)/40)^3 := by
        apply pow_le_pow_left₀ (by positivity) hD_div 3
      calc
        1000 * Real.log (T:ℝ) = (10 * ((Real.log (T:ℝ)) ^ ((1:ℝ)/3)))^3 := by
          rw [show (10 * ((Real.log (T:ℝ)) ^ ((1:ℝ)/3)))^3 = 1000 * (((Real.log (T:ℝ)) ^ ((1:ℝ)/3))^3) by ring]
          rw [hr_cube]
        _ ≤ ((D:ℝ)/40)^3 := hmono
    have hexp_le : Real.exp (-(((D:ℝ)/40)^3)) ≤ (T:ℝ)^(-1000:ℝ) := by
      have h1 : Real.exp (-(((D:ℝ)/40)^3)) ≤ Real.exp (-(1000 * Real.log (T:ℝ))) := by
        apply Real.exp_le_exp.mpr
        linarith
      have h2 : Real.exp (-(1000 * Real.log (T:ℝ))) = (T:ℝ)^(-1000:ℝ) := by
        rw [Real.rpow_def_of_pos hTpos]
        congr 1
        ring
      exact h1.trans_eq h2
    have htail1 : 12 * (T:ℝ) * Real.exp (-(((D:ℝ)/40)^3)) ≤ 12 * (T:ℝ) * (T:ℝ)^(-1000:ℝ) := by
      apply mul_le_mul_of_nonneg_left hexp_le
      positivity
    have hT_mul : (T:ℝ) * (T:ℝ)^(-1000:ℝ) = (T:ℝ)^(-999:ℝ) := by
      calc
        (T:ℝ) * (T:ℝ)^(-1000:ℝ) = (T:ℝ)^(1:ℝ) * (T:ℝ)^(-1000:ℝ) := by rw [Real.rpow_one]
        _ = (T:ℝ)^((1:ℝ) + (-1000:ℝ)) := by rw [Real.rpow_add hTpos]
        _ = (T:ℝ)^(-999:ℝ) := by norm_num
    have h12le : (12:ℝ) ≤ (T:ℝ)^998 := by
      have hpow : (2:ℝ)^998 ≤ (T:ℝ)^998 := pow_le_pow_left₀ (by norm_num) hTreal 998
      have h12_2pow : (12:ℝ) ≤ (2:ℝ)^998 := by
        calc
          (12:ℝ) ≤ (2:ℝ)^4 := by norm_num
          _ ≤ (2:ℝ)^998 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by norm_num : 4 ≤ 998)
      exact le_trans h12_2pow hpow
    have hpow_mul : (T:ℝ)^998 * (T:ℝ)^(-999:ℝ) = (T:ℝ)^(-1:ℝ) := by
      calc
        (T:ℝ)^998 * (T:ℝ)^(-999:ℝ) = (T:ℝ)^(998:ℝ) * (T:ℝ)^(-999:ℝ) := by norm_num
        _ = (T:ℝ)^((998:ℝ) + (-999:ℝ)) := by rw [Real.rpow_add hTpos]
        _ = (T:ℝ)^(-1:ℝ) := by norm_num
    have htail2 : 12 * (T:ℝ) * (T:ℝ)^(-1000:ℝ) ≤ (T:ℝ)^(-1:ℝ) := by
      calc
        12 * (T:ℝ) * (T:ℝ)^(-1000:ℝ) = 12 * ((T:ℝ) * (T:ℝ)^(-1000:ℝ)) := by ring
        _ = 12 * (T:ℝ)^(-999:ℝ) := by rw [hT_mul]
        _ ≤ (T:ℝ)^998 * (T:ℝ)^(-999:ℝ) := by
          apply mul_le_mul_of_nonneg_right h12le
          exact Real.rpow_nonneg (by positivity) _
        _ = (T:ℝ)^(-1:ℝ) := hpow_mul
    exact le_trans htail1 htail2
