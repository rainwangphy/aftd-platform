import AFTD.Prelude

/-!
# energy_filter_tendsto_zero_of_sq_le_product

Topic: statistical_mechanics   Node: bfe9ac7f643c

Provenance: helper lemma. OP-892: convergence of shifted binomial kernels.

If A converges to a finite real number, D tends to zero, and R squared is eventually at most A times D, then R tends to zero.
-/

theorem energy_filter_tendsto_zero_of_sq_le_product
    (R A D : ℕ → ℝ) (a : ℝ)
    (hA : Filter.Tendsto A Filter.atTop (nhds a))
    (hD : Filter.Tendsto D Filter.atTop (nhds 0))
    (hbound : ∀ᶠ k in Filter.atTop, (R k) ^ 2 ≤ A k * D k) :
    Filter.Tendsto R Filter.atTop (nhds 0) := by
  have hprod : Filter.Tendsto (fun k => A k * D k) Filter.atTop (nhds 0) := by
    simpa using hA.mul hD
  have hsq : Filter.Tendsto (fun k => (R k)^2) Filter.atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun k => sq_nonneg (R k)) hbound hprod
  have habs : Filter.Tendsto (fun k => |R k|) Filter.atTop (nhds 0) := by
    have hroot : Filter.Tendsto (fun k => Real.sqrt (R k ^ 2)) Filter.atTop (nhds 0) := by
      change Filter.Tendsto ((fun x : ℝ => Real.sqrt x) ∘ fun k => R k ^ 2) Filter.atTop (nhds 0)
      simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hsq
    have he : (fun k => Real.sqrt (R k ^ 2)) = (fun k => |R k|) := by
      funext k
      exact Real.sqrt_sq_eq_abs (R k)
    rwa [he] at hroot
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
