import AFTD.Prelude
import AFTD.Kb.Tcs.PowerDivergenceGenerator
import AFTD.Kb.Tcs.MutualFInformation
import AFTD.Kb.Tcs.MutualPowerDivergenceInformationEqSumRpow

/-!
# power_divergence_exists_binary_counterexample_of_lt_golden_ratio

Topic: information   Node: aa3f4a5702b8

Provenance: formalization of a published result. Source: arXiv:2610.21231, On the Subadditivity of Mutual f-Information; Open Problem OP-726

For every exponent beta in (0, (sqrt 5 - 1)/2), there exist strictly positive binary probability mass functions pX, PY, PZ forming a Markov chain Y <- X -> Z such that mutual power-divergence information subadditivity strictly fails.
-/

theorem pdgold_L_pos (β : ℝ) (hβ0 : 0 < β) (hβ : β < (Real.sqrt 5 - 1) / 2) :
    ∃ a κ : ℝ, 0 < a ∧ a < 1 ∧ 0 < κ ∧
      0 < -(1 - β) * a ^ 2 - (1 - (1 - a) ^ β) ^ 2 +
        2 * κ ^ β * ((a + κ) ^ (1 - β) - (κ + a - a * a) ^ (1 - β)) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hq : β ^ 2 + β < 1 := by nlinarith
  have hβ1 : β < 1 := by nlinarith
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = (1 - β - β ^ 2) / 4 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha_def]; nlinarith
  have ha1 : a < 1 / 4 := by rw [ha_def]; nlinarith
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (1 - β) * (1 - a) ^ 2 - β ^ 2 := ⟨_, rfl⟩
  have hD0 : 0 < D := by
    rw [hD]
    have : (1 - a) ^ 2 ≥ 1 - 2 * a := by nlinarith
    have : (1 - β) * (1 - 2 * a) - β ^ 2 = (1 + β) * (1 - β - β ^ 2) / 2 := by rw [ha_def]; ring
    nlinarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = a * ((1 - β) * (1 - a) ^ 2 + β ^ 2) / D + 1 := ⟨_, rfl⟩
  have hκ1 : 1 ≤ κ := by
    rw [hκ]; have : 0 ≤ a * ((1 - β) * (1 - a) ^ 2 + β ^ 2) / D := by positivity
    linarith
  have hκ0 : 0 < κ := by linarith
  refine ⟨a, κ, ha0, by linarith, hκ0, ?_⟩
  -- (i) 0 ≤ 1 - (1-a)^β ≤ β a / (1 - a)
  have h1a : 0 < 1 - a := by linarith
  have hA0 : (1 - a) ^ β ≤ 1 := Real.rpow_le_one h1a.le (by linarith) hβ0.le
  have hA1 : 1 - β * (a / (1 - a)) ≤ (1 - a) ^ β := by
    have hb := rpow_one_add_le_one_add_mul_self (s := a / (1 - a)) (by
      have : 0 ≤ a / (1 - a) := by positivity
      linarith) hβ0.le hβ1.le
    have h11 : 1 + a / (1 - a) = (1 - a)⁻¹ := by field_simp; ring
    rw [h11, Real.inv_rpow h1a.le] at hb
    have hpos : 0 < (1 - a) ^ β := Real.rpow_pos_of_pos h1a β
    have hpos' : 0 ≤ β * (a / (1 - a)) := by positivity
    rw [inv_le_iff_one_le_mul₀' hpos] at hb
    nlinarith
  -- (ii) concavity: (x - a^2)^γ ≤ x^γ - γ x^γ a^2 / x
  have hx0 : 0 < a + κ := by linarith
  have hy0 : 0 < κ + a - a * a := by nlinarith
  have hB : (κ + a - a * a) ^ (1 - β) ≤ (a + κ) ^ (1 - β) * (1 + (1 - β) * (-(a * a) / (a + κ))) := by
    have hb := rpow_one_add_le_one_add_mul_self (s := -(a * a) / (a + κ)) (by
      rw [neg_div, neg_le_neg_iff, div_le_one hx0]; nlinarith) (by linarith : (0:ℝ) ≤ 1 - β) (by linarith)
    have h11 : κ + a - a * a = (a + κ) * (1 + -(a * a) / (a + κ)) := by field_simp; ring
    rw [h11, Real.mul_rpow hx0.le (by rw [← mul_le_mul_iff_of_pos_left hx0, mul_zero, ← h11]; exact hy0.le)]
    exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx0.le _)
  -- κ^β (a+κ)^(1-β) / (a+κ) ≥ κ / (a+κ)
  have hC : κ / (a + κ) ≤ κ ^ β * (a + κ) ^ (1 - β) / (a + κ) := by
    have hr : κ / (a + κ) ≤ (κ / (a + κ)) ^ β := by
      have := Real.rpow_le_rpow_of_exponent_ge (by positivity : 0 < κ / (a + κ))
        (by rw [div_le_one hx0]; linarith) hβ1.le
      simpa using this
    have he : (κ / (a + κ)) ^ β = κ ^ β * (a + κ) ^ (1 - β) / (a + κ) := by
      rw [Real.div_rpow hκ0.le hx0.le, Real.rpow_sub hx0, Real.rpow_one]
      field_simp
    linarith
  have hKpos : 0 ≤ κ ^ β := Real.rpow_nonneg hκ0.le _
  have hXpos : 0 ≤ (a + κ) ^ (1 - β) := Real.rpow_nonneg hx0.le _
  -- combine
  have hmain : 2 * (1 - β) * (a * a) * (κ / (a + κ)) ≤
      2 * κ ^ β * ((a + κ) ^ (1 - β) - (κ + a - a * a) ^ (1 - β)) := by
    have e1 : (a + κ) ^ (1 - β) * (1 + (1 - β) * (-(a * a) / (a + κ))) =
        (a + κ) ^ (1 - β) - (1 - β) * (a * a) * ((a + κ) ^ (1 - β) / (a + κ)) := by ring
    rw [e1] at hB
    have e2 : κ ^ β * ((a + κ) ^ (1 - β) / (a + κ)) = κ ^ β * (a + κ) ^ (1 - β) / (a + κ) := by ring
    have h3 : (1 - β) * (a * a) * (κ / (a + κ)) ≤
        (1 - β) * (a * a) * (κ ^ β * ((a + κ) ^ (1 - β) / (a + κ))) := by
      rw [e2]; exact mul_le_mul_of_nonneg_left hC (by nlinarith)
    linarith [mul_le_mul_of_nonneg_left hB hKpos]
  have hsq : (1 - (1 - a) ^ β) ^ 2 ≤ (β * (a / (1 - a))) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  -- polynomial part
  have hpoly : 0 < -(1 - β) * a ^ 2 - (β * (a / (1 - a))) ^ 2 + 2 * (1 - β) * (a * a) * (κ / (a + κ)) := by
    have e : -(1 - β) * a ^ 2 - (β * (a / (1 - a))) ^ 2 + 2 * (1 - β) * (a * a) * (κ / (a + κ)) =
        a ^ 2 * ((1 - β) * (1 - a) ^ 2 * (κ - a) - β ^ 2 * (κ + a)) / ((1 - a) ^ 2 * (a + κ)) := by
      field_simp; ring
    rw [e]
    apply div_pos _ (by positivity)
    apply mul_pos (by positivity)
    have : κ * D = a * ((1 - β) * (1 - a) ^ 2 + β ^ 2) + D := by
      rw [hκ]; field_simp
    have e2 : (1 - β) * (1 - a) ^ 2 * (κ - a) - β ^ 2 * (κ + a) =
        κ * D - a * ((1 - β) * (1 - a) ^ 2 + β ^ 2) := by rw [hD]; ring
    rw [e2]; linarith
  linarith

theorem pdgold_channel_form {X Y : Type*} [Fintype X] [Fintype Y] (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (pX : X → ℝ) (W : X → Y → ℝ) (hpX : ∀ x, 0 ≤ pX x) (hpX1 : ∑ x, pX x = 1)
    (hW : ∀ x y, 0 ≤ W x y) (hW1 : ∀ x, ∑ y, W x y = 1) :
    mutual_f_information (power_divergence_generator β) (fun x y => pX x * W x y) =
      (∑ x, ∑ y, pX x * (W x y ^ β * (∑ x', pX x' * W x' y) ^ (1 - β)) - 1) / (β * (β - 1)) := by
  rw [mutual_power_divergence_information_eq_sum_rpow β hβ0 hβ1 _
    (fun x y => mul_nonneg (hpX x) (hW x y))
    (by simp_rw [← Finset.mul_sum, hW1, mul_one, hpX1])]
  congr 2
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum, hW1, mul_one, Real.mul_rpow (hpX x) (hW x y),
    Real.mul_rpow (hpX x) (Finset.sum_nonneg fun x' _ => mul_nonneg (hpX x') (hW x' y))]
  have : pX x ^ β * pX x ^ (1 - β) = pX x := by
    rw [← Real.rpow_add' (hpX x) (by norm_num), add_sub_cancel, Real.rpow_one]
  calc pX x ^ β * W x y ^ β * (pX x ^ (1 - β) * (∑ x', pX x' * W x' y) ^ (1 - β))
      = (pX x ^ β * pX x ^ (1 - β)) * (W x y ^ β * (∑ x', pX x' * W x' y) ^ (1 - β)) := by ring
    _ = _ := by rw [this]

theorem pdgold_hasDerivAt_mul_of_continuousAt {h : ℝ → ℝ} (hh : ContinuousAt h 0) :
    HasDerivAt (fun p => p * h p) (h 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine (hh.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hp
  have hp' : p ≠ 0 := hp
  rw [slope_def_field]
  field_simp
  simp

theorem pdgold_exists_pos_of_hasDerivAt {G : ℝ → ℝ} {L : ℝ} (hG : HasDerivAt G L 0) (h0 : G 0 = 0)
    (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) : ∃ p, 0 < p ∧ p < ε ∧ 0 < G p := by
  rw [hasDerivAt_iff_tendsto_slope] at hG
  have h1 := (hG.mono_left (nhdsWithin_mono _ (by
    intro x hx; exact Set.mem_compl_singleton_iff.mpr (ne_of_gt hx) : Set.Ioi (0:ℝ) ⊆ {0}ᶜ))).eventually
    (lt_mem_nhds hL)
  have h2 : ∀ᶠ p in nhdsWithin (0:ℝ) (Set.Ioi 0), p ∈ Set.Ioo 0 ε := Ioo_mem_nhdsGT hε
  obtain ⟨p, hp1, hp2⟩ := (h1.and h2).exists
  refine ⟨p, hp2.1, hp2.2, ?_⟩
  rw [slope_def_field, h0, sub_zero, sub_zero] at hp1
  exact (div_pos_iff_of_pos_right hp2.1).mp hp1

theorem pdgold_deriv_c0 (β a κ : ℝ) :
    HasDerivAt (fun p : ℝ => (1 - p) * ((1 - κ * p) ^ β * ((1 - p) * (1 - κ * p) + p * (1 - a)) ^ (1 - β)))
      (-1 - β * κ - (1 - β) * (κ + a)) 0 := by
  have d1 : HasDerivAt (fun p : ℝ => 1 - κ * p) (-(κ * 1)) 0 := ((hasDerivAt_id' 0).const_mul κ).const_sub 1
  have dq : HasDerivAt (fun p : ℝ => (1 - p) * (1 - κ * p) + p * (1 - a))
      (-1 * (1 - κ * 0) + (1 - 0) * (-(κ * 1)) + 1 * (1 - a)) 0 :=
    ((((hasDerivAt_id' 0).const_sub 1).mul d1).add ((hasDerivAt_id' 0).mul_const (1 - a)))
  have := ((hasDerivAt_id' (0:ℝ)).const_sub 1).mul
    ((d1.rpow_const (p := β) (Or.inl (by simp))).mul (dq.rpow_const (p := 1 - β) (Or.inl (by simp))))
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.add_apply, mul_zero, sub_zero, zero_mul, add_zero, Real.one_rpow, mul_one,
    one_mul]
  ring

theorem pdgold_deriv_c00 (β a κ : ℝ) :
    HasDerivAt (fun p : ℝ => (1 - p) * (((1 - κ * p) * (1 - κ * p)) ^ β *
        ((1 - p) * ((1 - κ * p) * (1 - κ * p)) + p * ((1 - a) * (1 - a))) ^ (1 - β)))
      (-1 - 2 * β * κ + (1 - β) * (-1 - 2 * κ + (1 - a) * (1 - a))) 0 := by
  have d1 : HasDerivAt (fun p : ℝ => 1 - κ * p) (-(κ * 1)) 0 := ((hasDerivAt_id' 0).const_mul κ).const_sub 1
  have d2 := d1.mul d1
  have dq := (((hasDerivAt_id' 0).const_sub 1).mul d2).add ((hasDerivAt_id' (0:ℝ)).mul_const ((1 - a) * (1 - a)))
  have := ((hasDerivAt_id' (0:ℝ)).const_sub 1).mul
    ((d2.rpow_const (p := β) (Or.inl (by simp))).mul (dq.rpow_const (p := 1 - β) (Or.inl (by simp))))
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.add_apply, mul_zero, sub_zero, zero_mul, add_zero, Real.one_rpow, mul_one,
    one_mul]
  ring

/-- The remainder coefficient. -/
noncomputable def pdgold_golden_cex_K (β a κ p : ℝ) : ℝ :=
  2 * ((1 - a) ^ β * ((1 - p) * (1 - κ * p) + p * (1 - a)) ^ (1 - β) +
      (1 - p) * (κ ^ β * (a + (1 - p) * κ) ^ (1 - β)) +
      p ^ (1 - β) * (a ^ β * (a + (1 - p) * κ) ^ (1 - β))) -
    (((1 - a) * (1 - a)) ^ β *
        ((1 - p) * ((1 - κ * p) * (1 - κ * p)) + p * ((1 - a) * (1 - a))) ^ (1 - β) +
      (1 - p) * (((1 - κ * p) * κ) ^ β * ((1 - p) * (1 - κ * p) * κ + (1 - a) * a) ^ (1 - β)) +
      (1 - p) * ((κ * (1 - κ * p)) ^ β * ((1 - p) * (1 - κ * p) * κ + (1 - a) * a) ^ (1 - β)) +
      (1 - p) * (p ^ β * ((κ * κ) ^ β * ((1 - p) * κ * κ * p + a * a) ^ (1 - β))) +
      p ^ (1 - β) * (((1 - a) * a) ^ β * ((1 - p) * (1 - κ * p) * κ + (1 - a) * a) ^ (1 - β)) +
      p ^ (1 - β) * ((a * (1 - a)) ^ β * ((1 - p) * (1 - κ * p) * κ + (1 - a) * a) ^ (1 - β)) +
      p ^ (1 - β) * ((a * a) ^ β * ((1 - p) * κ * κ * p + a * a) ^ (1 - β)))

theorem pdgold_K_cont (β a κ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) : Continuous (pdgold_golden_cex_K β a κ) := by
  have h1 : (0:ℝ) ≤ 1 - β := by linarith
  have h2 : (0:ℝ) ≤ β := hβ0.le
  unfold pdgold_golden_cex_K
  fun_prop (disch := assumption)

theorem pdgold_K_zero (β a κ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (ha1 : a < 1) :
    pdgold_golden_cex_K β a κ 0 = 2 * ((1 - a) ^ β + κ ^ β * (a + κ) ^ (1 - β)) -
      ((1 - a) ^ β * (1 - a) ^ β + 2 * (κ ^ β * (κ + a - a * a) ^ (1 - β))) := by
  have h1β : (1:ℝ) - β ≠ 0 := by linarith
  unfold pdgold_golden_cex_K
  simp only [mul_zero, sub_zero, zero_mul, add_zero, one_mul, mul_one, Real.zero_rpow h1β,
    Real.zero_rpow hβ0.ne', Real.one_rpow, zero_add]
  rw [Real.mul_rpow (by linarith : (0:ℝ) ≤ 1 - a) (by linarith : (0:ℝ) ≤ 1 - a),
    show κ + (1 - a) * a = κ + a - a * a by ring]
  ring

/-- Strictly positive binary counterexample to subadditivity for every beta < (sqrt 5 - 1) / 2. -/
theorem power_divergence_exists_binary_counterexample_of_lt_golden_ratio (β : ℝ)
    (hβ0 : 0 < β) (hβ : β < (Real.sqrt 5 - 1) / 2) :
    ∃ (pX : Fin 2 → ℝ) (PY PZ : Fin 2 → Fin 2 → ℝ),
      (∀ x, 0 < pX x) ∧ (∑ x, pX x = 1) ∧
      (∀ x y, 0 < PY x y) ∧ (∀ x, ∑ y, PY x y = 1) ∧
      (∀ x z, 0 < PZ x z) ∧ (∀ x, ∑ z, PZ x z = 1) ∧
      mutual_f_information (power_divergence_generator β) (fun x y => pX x * PY x y) +
          mutual_f_information (power_divergence_generator β) (fun x z => pX x * PZ x z) <
        mutual_f_information (power_divergence_generator β) (fun x (yz : Fin 2 × Fin 2) => pX x * PY x yz.1 * PZ x yz.2) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hβ1 : β < 1 := by nlinarith [Real.sqrt_nonneg 5]
  obtain ⟨a, κ, ha0, ha1, hκ0, hL⟩ := pdgold_L_pos β hβ0 hβ
  have hG := ((((pdgold_deriv_c0 β a κ).const_mul 2).sub_const 1).sub (pdgold_deriv_c00 β a κ)).add
    (pdgold_hasDerivAt_mul_of_continuousAt (pdgold_K_cont β a κ hβ0 hβ1).continuousAt)
  have hL' : 0 < 2 * (-1 - β * κ - (1 - β) * (κ + a)) -
      (-1 - 2 * β * κ + (1 - β) * (-1 - 2 * κ + (1 - a) * (1 - a))) + pdgold_golden_cex_K β a κ 0 := by
    rw [pdgold_K_zero β a κ hβ0 hβ1 ha1]
    have : 2 * (-1 - β * κ - (1 - β) * (κ + a)) -
        (-1 - 2 * β * κ + (1 - β) * (-1 - 2 * κ + (1 - a) * (1 - a))) +
        (2 * ((1 - a) ^ β + κ ^ β * (a + κ) ^ (1 - β)) -
          ((1 - a) ^ β * (1 - a) ^ β + 2 * (κ ^ β * (κ + a - a * a) ^ (1 - β)))) =
        -(1 - β) * a ^ 2 - (1 - (1 - a) ^ β) ^ 2 +
          2 * κ ^ β * ((a + κ) ^ (1 - β) - (κ + a - a * a) ^ (1 - β)) := by ring
    linarith
  obtain ⟨p, hp, hpε, hGp⟩ := pdgold_exists_pos_of_hasDerivAt hG (by norm_num) hL' (1 / (2 * (κ + 1)))
    (by positivity)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at hGp
  have hp1 : p < 1 / 2 := by
    calc p < 1 / (2 * (κ + 1)) := hpε
      _ ≤ 1 / 2 := by gcongr; linarith
  have hkp : κ * p < 1 / 2 := by
    have : p * (2 * (κ + 1)) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hpε
    nlinarith
  have h1k : 0 < 1 - κ * p := by linarith
  have h1p : 0 < 1 - p := by linarith
  have h1a : 0 < 1 - a := by linarith
  set pX : Fin 2 → ℝ := ![1 - p, p] with hpXdef
  set W : Fin 2 → Fin 2 → ℝ := ![![1 - κ * p, κ * p], ![1 - a, a]] with hWdef
  have hpXpos : ∀ x, 0 < pX x := by
    intro x; fin_cases x <;> simp [pX] <;> linarith
  have hpX1 : ∑ x, pX x = 1 := by simp [pX, Fin.sum_univ_two]
  have hWpos : ∀ x y, 0 < W x y := by
    intro x y; fin_cases x <;> fin_cases y <;> simp [W] <;> first | linarith | positivity
  have hW1 : ∀ x, ∑ y, W x y = 1 := by
    intro x; fin_cases x <;> simp [W, Fin.sum_univ_two]
  refine ⟨pX, W, W, hpXpos, hpX1, hWpos, hW1, hWpos, hW1, ?_⟩
  have hYZfun : (fun x (yz : Fin 2 × Fin 2) => pX x * W x yz.1 * W x yz.2) =
      fun x yz => pX x * (W x yz.1 * W x yz.2) := by
    funext x yz; ring
  rw [hYZfun, pdgold_channel_form β hβ0 hβ1 pX W (fun x => (hpXpos x).le) hpX1
      (fun x y => (hWpos x y).le) hW1,
    pdgold_channel_form β hβ0 hβ1 pX (fun x (yz : Fin 2 × Fin 2) => W x yz.1 * W x yz.2)
      (fun x => (hpXpos x).le) hpX1 (fun x yz => mul_nonneg (hWpos x yz.1).le (hWpos x yz.2).le)
      (by intro x; rw [Fintype.sum_prod_type]; simp only [← Finset.mul_sum, hW1, mul_one])]
  set SY := ∑ x, ∑ y, pX x * (W x y ^ β * (∑ x', pX x' * W x' y) ^ (1 - β)) with hSY
  set SYZ := ∑ x, ∑ yz : Fin 2 × Fin 2, pX x * ((W x yz.1 * W x yz.2) ^ β *
      (∑ x', pX x' * (W x' yz.1 * W x' yz.2)) ^ (1 - β)) with hSYZ
  have hS : 0 < 2 * SY - 1 - SYZ := by
    rw [hSY, hSYZ]
    simp only [pX, W, Fin.sum_univ_two, Fintype.sum_prod_type, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    unfold pdgold_golden_cex_K at hGp
    convert hGp using 1
    rw [show (1 - p) * (κ * p) + p * a = p * (a + (1 - p) * κ) by ring,
      show (1 - p) * ((1 - κ * p) * (κ * p)) + p * ((1 - a) * a) =
        p * ((1 - p) * (1 - κ * p) * κ + (1 - a) * a) by ring,
      show (1 - p) * (κ * p * (1 - κ * p)) + p * (a * (1 - a)) =
        p * ((1 - p) * (1 - κ * p) * κ + (1 - a) * a) by ring,
      show (1 - p) * (κ * p * (κ * p)) + p * (a * a) = p * ((1 - p) * κ * κ * p + a * a) by ring,
      show (1 - κ * p) * (κ * p) = (1 - κ * p) * κ * p by ring,
      show κ * p * (1 - κ * p) = κ * (1 - κ * p) * p by ring,
      show κ * p * (κ * p) = κ * κ * (p * p) by ring]
    have hk := hκ0.le
    have hpp := hp.le
    rw [Real.mul_rpow hk hpp, Real.mul_rpow (mul_nonneg h1k.le hk) hpp,
      Real.mul_rpow (mul_nonneg hk h1k.le) hpp, Real.mul_rpow (mul_nonneg hk hk) (mul_nonneg hpp hpp),
      Real.mul_rpow hpp hpp, Real.mul_rpow hpp (add_nonneg ha0.le (mul_nonneg h1p.le hk)),
      Real.mul_rpow hpp (add_nonneg (mul_nonneg (mul_nonneg h1p.le h1k.le) hk) (mul_nonneg h1a.le ha0.le)),
      Real.mul_rpow hpp (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1p.le hk) hk) hpp)
        (mul_nonneg ha0.le ha0.le)),
      Real.rpow_sub hp 1 β, Real.rpow_one]
    have hP : 0 < p ^ β := Real.rpow_pos_of_pos hp β
    field_simp
    ring_nf
  have hc : β * (β - 1) < 0 := by nlinarith
  have e : (SYZ - 1) / (β * (β - 1)) - ((SY - 1) / (β * (β - 1)) + (SY - 1) / (β * (β - 1))) =
      (2 * SY - 1 - SYZ) / (-(β * (β - 1))) := by
    field_simp
    ring
  have : 0 < (SYZ - 1) / (β * (β - 1)) - ((SY - 1) / (β * (β - 1)) + (SY - 1) / (β * (β - 1))) := by
    rw [e]; exact div_pos hS (by linarith)
  linarith
