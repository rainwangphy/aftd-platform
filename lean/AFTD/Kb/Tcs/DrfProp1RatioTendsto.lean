import AFTD.Prelude
import AFTD.Kb.Tcs.DrfProp1Ratio
import AFTD.Kb.Tcs.DrfProp1K

/-!
# drf_prop1_ratio_tendsto

Topic: online_algorithms   Node: 588d893f79b4

Provenance: formalization of a published result. Source: arXiv:2611.07905 Proposition 1

For every natural number D with 1 ≤ D, the sequence `fun m : ℕ => drf_prop1_ratio D m` converges to `1 + Real.sqrt (D : ℝ)` along `Filter.atTop`.
-/

lemma drf_prop1_ratio_tendsto_k_div (D : ℕ) :
    Filter.Tendsto (fun m : ℕ => (drf_prop1_k D m : ℝ) / (m : ℝ)) Filter.atTop (nhds (Real.sqrt (D : ℝ))) := by
  set c := Real.sqrt (D : ℝ)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have h_lower : Filter.Tendsto (fun m : ℕ => c - (m : ℝ)⁻¹) Filter.atTop (nhds c) := by
    have h := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub c
    simpa using h
  have h_upper : Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (nhds c) := tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower h_upper ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with m hm
    have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    dsimp [drf_prop1_k]
    have h1 := Nat.sub_one_lt_floor ((m : ℝ) * c)
    rw [inv_eq_one_div]
    have : c - 1 / (m : ℝ) = ((m : ℝ) * c - 1) / (m : ℝ) := by
      rw [sub_div, mul_div_cancel_left₀ c hm_pos.ne']
    rw [this]
    exact (div_le_div_iff_of_pos_right hm_pos).mpr h1.le
  · filter_upwards [Filter.eventually_gt_atTop 0] with m hm
    have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    dsimp [drf_prop1_k]
    have h2 : (Nat.floor ((m : ℝ) * c) : ℝ) ≤ (m : ℝ) * c :=
      Nat.floor_le (mul_nonneg hm_pos.le hc)
    rw [div_le_iff₀ hm_pos]
    linarith

/-- As m tends to infinity, the ratio of DRF completion time to the offline bound converges to 1 + sqrt(D). -/
theorem drf_prop1_ratio_tendsto (D : ℕ) (hD : 1 ≤ D) : Filter.Tendsto (fun m : ℕ => drf_prop1_ratio D m) Filter.atTop (nhds (1 + Real.sqrt (D : ℝ))) := by
  set u := fun m : ℕ => (drf_prop1_k D m : ℝ) / (m : ℝ)
  set v := fun m : ℕ => 1 / (m : ℝ)
  have hu : Filter.Tendsto u Filter.atTop (nhds (Real.sqrt (D : ℝ))) := drf_prop1_ratio_tendsto_k_div D
  have hv : Filter.Tendsto v Filter.atTop (nhds (0 : ℝ)) := by
    have h : Filter.Tendsto (fun m : ℕ => (m : ℝ)⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [v, one_div] using h
  set num := fun m : ℕ => ((D : ℝ) + u m) * (1 + u m)
  set den := fun m : ℕ => (D : ℝ) * (1 + v m) / 2 + u m + u m * (u m + v m) / 2
  have hnum : Filter.Tendsto num Filter.atTop (nhds (((D : ℝ) + Real.sqrt (D : ℝ)) * (1 + Real.sqrt (D : ℝ)))) := by
    exact ((tendsto_const_nhds (x := (D : ℝ))).add hu).mul ((tendsto_const_nhds (x := (1 : ℝ))).add hu)
  have hden_raw : Filter.Tendsto den Filter.atTop
      (nhds ((D : ℝ) * (1 + 0) / 2 + Real.sqrt (D : ℝ) + Real.sqrt (D : ℝ) * (Real.sqrt (D : ℝ) + 0) / 2)) := by
    refine (((tendsto_const_nhds (x := (D : ℝ))).mul ((tendsto_const_nhds (x := (1 : ℝ))).add hv)).div_const (2 : ℝ)).add hu |>.add ?_
    exact (hu.mul (hu.add hv)).div_const (2 : ℝ)
  have hden_eq : (D : ℝ) * (1 + 0) / 2 + Real.sqrt (D : ℝ) + Real.sqrt (D : ℝ) * (Real.sqrt (D : ℝ) + 0) / 2 =
      (D : ℝ) + Real.sqrt (D : ℝ) := by
    have hsq : Real.sqrt (D : ℝ) * Real.sqrt (D : ℝ) = (D : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg D)
    linear_combination 1/2 * hsq
  rw [hden_eq] at hden_raw
  have hden_ne_zero : (D : ℝ) + Real.sqrt (D : ℝ) ≠ 0 := by
    have : 1 ≤ (D : ℝ) := by exact_mod_cast hD
    positivity
  have hdiv := hnum.div hden_raw hden_ne_zero
  have hdiv_simp : (((D : ℝ) + Real.sqrt (D : ℝ)) * (1 + Real.sqrt (D : ℝ))) / ((D : ℝ) + Real.sqrt (D : ℝ)) =
      1 + Real.sqrt (D : ℝ) :=
    mul_div_cancel_left₀ (1 + Real.sqrt (D : ℝ)) hden_ne_zero
  rw [hdiv_simp] at hdiv
  refine Filter.Tendsto.congr' ?_ hdiv
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  dsimp [num, den, u, v, drf_prop1_ratio, drf_prop1_alg, drf_prop1_opt_bound]
  have hm_pos : (m : ℝ) ≠ 0 := by
    have : 0 < m := hm
    positivity
  field_simp
