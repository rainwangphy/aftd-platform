import AFTD.Prelude

/-!
# energy_filter_step_sum_integral

Topic: statistical_mechanics   Node: de526feb3cb6

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

For a finite set of integers, real weights w, and positive h, the integral of the sum of w(i) times the indicator of [i/h,(i+1)/h) equals the sum of the weights divided by h.
-/

theorem energy_filter_step_sum_integral
    (s : Finset ℤ) (w : ℤ → ℝ) (h : ℝ) (hh : 0 < h) :
    (∫ x : ℝ, ∑ i ∈ s,
      (Set.Ico ((i:ℝ)/h) (((i:ℝ)+1)/h)).indicator (fun _ : ℝ => w i) x) =
      (∑ i ∈ s, w i) / h := by
  have hf (i : ℤ) : MeasureTheory.Integrable (fun x : ℝ =>
      (Set.Ico ((i:ℝ)/h) (((i:ℝ)+1)/h)).indicator (fun _ : ℝ => w i) x) := by
    apply MeasureTheory.IntegrableOn.integrable_indicator _ measurableSet_Ico
    exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ico])
  rw [MeasureTheory.integral_finsetSum s (fun i hi => hf i), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hab : (i:ℝ)/h ≤ ((i:ℝ)+1)/h := by gcongr; linarith
  rw [MeasureTheory.integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico_of_le hab]
  simp only [smul_eq_mul]
  field_simp
  ring
