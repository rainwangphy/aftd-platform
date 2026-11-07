import AFTD.Prelude

/-!
# energy_filter_critical_window_length_scale

Topic: statistical_mechanics   Node: f2458cf80cd4

Provenance: original. Related work: arXiv:2405.02158, Energy-filtered quantum states and the emergence of non-local correlations

For any c > 0, the normalized critical window length floor(c * sqrt(4k)) / sqrt(4k) converges to c as k tends to infinity.
-/

/-- The normalized critical window length m_k / sqrt(4k) converges to c as k tends to infinity. -/
theorem energy_filter_critical_window_length_scale (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto
      (fun k : ℕ => ((Nat.floor (c * Real.sqrt (4 * (k : ℝ))) : ℕ) : ℝ) / Real.sqrt (4 * (k : ℝ)))
      Filter.atTop
      (nhds c) := by
  have h4 : (0:ℝ) < 4 := by norm_num
  have hlin : Filter.Tendsto (fun k : ℕ => 4 * (k : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop h4 tendsto_natCast_atTop_atTop
  have hs : Filter.Tendsto (fun k : ℕ => Real.sqrt (4 * (k : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hlin
  have hx : Filter.Tendsto (fun k : ℕ => c * Real.sqrt (4 * (k : ℝ))) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc hs
  have hg : Filter.Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ) / x) Filter.atTop (nhds 1) :=
    tendsto_nat_floor_div_atTop
  have hgc : Filter.Tendsto
      (fun k : ℕ => ((⌊c * Real.sqrt (4 * (k : ℝ))⌋₊ : ℝ)) / (c * Real.sqrt (4 * (k : ℝ))))
      Filter.atTop (nhds 1) := hg.comp hx
  have hmul : Filter.Tendsto
      (fun k : ℕ => ((⌊c * Real.sqrt (4 * (k : ℝ))⌋₊ : ℝ) / (c * Real.sqrt (4 * (k : ℝ)))) * c)
      Filter.atTop (nhds (1 * c)) := hgc.mul_const c
  rw [one_mul] at hmul
  refine hmul.congr' (Filter.eventually_atTop.mpr ⟨1, fun k hk => ?_⟩)
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hs0 : Real.sqrt (4 * (k:ℝ)) ≠ 0 := by
    apply ne_of_gt
    rw [Real.sqrt_pos]
    positivity
  have hc0 : c ≠ 0 := ne_of_gt hc
  simp only
  field_simp
