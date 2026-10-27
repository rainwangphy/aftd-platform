import AFTD.Prelude

/-!
# redistribution_damped_cosine_integral

Topic: mechanism_design   Node: 812bed9db86f

Provenance: helper lemma. Routine analytic helper for IN-251, equation13 in the proof of arXiv:2610.10995 Lemma4.2. This supplies an exponential-regularization route to the absolute cosine kernel integral, avoiding a separate conditional sine integral. It does not prove the main error bound or a new research result.

For positive real damping a and any real frequency b, the exponentially damped cosine is absolutely integrable on the positive half-line and its integral is a/(a²+b²).
-/

open MeasureTheory

theorem redistribution_damped_cosine_integral
    (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => Real.exp (-a*u) * Real.cos (b*u)) (Set.Ioi 0) ∧
      (∫ u : ℝ in Set.Ioi 0, Real.exp (-a*u) * Real.cos (b*u)) =
        a / (a^2+b^2) := by
  set z : ℂ := (-(a:ℂ)) + (b:ℂ) * Complex.I with hz_def
  have hzre : z.re < 0 := by simp [hz_def, ha]
  have hf : MeasureTheory.IntegrableOn (fun u : ℝ => Complex.exp (z * u)) (Set.Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hzre 0
  have hcongr : ∀ u : ℝ, (Complex.exp (z * u)).re = Real.exp (-a*u) * Real.cos (b*u) := by
    intro u
    rw [Complex.exp_re]
    have h1 : (z * (u : ℂ)).re = -a*u := by simp [hz_def]
    have h2 : (z * (u : ℂ)).im = b*u := by simp [hz_def]
    rw [h1, h2]
  have hint : MeasureTheory.IntegrableOn (fun u : ℝ => (Complex.exp (z*u)).re) (Set.Ioi 0) :=
    ContinuousLinearMap.integrable_comp Complex.reCLM hf
  constructor
  · exact hint.congr (Filter.Eventually.of_forall (fun u => hcongr u))
  · rw [← MeasureTheory.setIntegral_congr_fun (measurableSet_Ioi) (fun u _ => hcongr u)]
    have hcomm : ∫ x : ℝ in Set.Ioi 0, (Complex.exp (z * x)).re
        = (∫ x : ℝ in Set.Ioi 0, Complex.exp (z * x)).re := by
      simpa using ContinuousLinearMap.integral_comp_comm Complex.reCLM hf
    rw [hcomm]
    rw [integral_exp_mul_complex_Ioi hzre 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div, Complex.neg_re,
      one_div, Complex.inv_re]
    have hzr : z.re = -a := by simp [hz_def]
    have hnorm : Complex.normSq z = a^2+b^2 := by
      rw [hz_def]
      have h := Complex.normSq_add_mul_I (-a) b
      rw [show ((-a:ℝ):ℂ) = -((a:ℝ):ℂ) by push_cast; ring] at h
      rw [h]
      ring
    rw [hzr, hnorm]
    ring
