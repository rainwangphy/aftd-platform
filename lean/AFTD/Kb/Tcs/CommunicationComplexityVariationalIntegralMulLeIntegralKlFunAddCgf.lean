import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityIntegrableExpSubCgf
import AFTD.Kb.Tcs.CommunicationComplexityIntegralExpSubCgfEqOne
import AFTD.Kb.Tcs.CommunicationComplexityMulLeKlFunAddExpSubOne

/-!
# CommunicationComplexity.variational_integral_mul_le_integral_klFun_add_cgf

Topic: information   Node: c09e2c2cf562

Provenance: helper lemma. TCSlib, `CommunicationComplexity.variational_integral_mul_le_integral_klFun_add_cgf`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A variational inequality for the mean of a random variable. Let $\mu$ be a probability measure on a measurable space $\Omega$, let $f, X : \Omega
\to \bbr$, and let $t \in \bbr$. Suppose that $f \ge 0$ pointwise, that $\int_\Omega
f\,d\mu = 1$, and that $f$, the map $x \mapsto f(x)\log f(x) - f(x) + 1$, the map $x
\mapsto e^{tX(x)}$, and the product $fX$ are all $\mu$-integrable. Writing $\Lambda(t) =
\log \int_\Omega e^{tX}\,d\mu$ for the cumulant generating function of $X$ under $\mu$,
one has
\[
t \int_\Omega f(x)\,X(x)\,d\mu(x) \;\le\; \int_\Omega \bigl(f(x)\log f(x) - f(x) +
1\bigr)\,d\mu(x) + \Lambda(t).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- Variational (Donsker–Varadhan-type) inequality: for a nonnegative density `f` with `∫ f dμ = 1` and any `X` with `exp (t X)` integrable, `t ∫ f X dμ ≤ ∫ klFun (f) dμ + cgf_X(t)`. **Proof sketch.** Write `c = cgf_X(t)`. Step 1: the pointwise bound `mul_le_klFun_add_exp_sub_one` with `u = f x`, `y = t X x − c` gives `f · (t X − c) ≤ klFun f + exp (t X − c) − 1`, and both sides are integrable; integrate. Step 2: the left integral is `t ∫ f X − c ∫ f = t ∫ f X − c`. Step 3: the right integral is `∫ klFun f + ∫ exp (t X − c) − 1 = ∫ klFun f`, since the tilted density integrates to `1`. Rearranging gives the claim. -/
theorem CommunicationComplexity.variational_integral_mul_le_integral_klFun_add_cgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f X : Ω → ℝ} {t : ℝ}
    (hf_int : Integrable f μ)
    (h_kl_int : Integrable (fun x => InformationTheory.klFun (f x)) μ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (h_integral : ∫ x, f x ∂μ = 1)
    (h_exp_int : Integrable (fun x => Real.exp (t * X x)) μ)
    (hfX_int : Integrable (fun x => f x * X x) μ) :
    t * ∫ x, f x * X x ∂μ ≤
      ∫ x, InformationTheory.klFun (f x) ∂μ + ProbabilityTheory.cgf X μ t := by
  let c := ProbabilityTheory.cgf X μ t
  -- Step 1: integrate the pointwise inequality
  have h_left_int :
      Integrable (fun x => f x * (t * X x - c)) μ := by
    have h1 : Integrable (fun x => t * (f x * X x)) μ := hfX_int.const_mul t
    have h2 : Integrable (fun x => c * f x) μ := hf_int.const_mul c
    convert h1.sub h2 using 2 with x
    simp only [Pi.sub_apply]; ring
  have h_right_int :
      Integrable (fun x =>
        InformationTheory.klFun (f x) + Real.exp (t * X x - c) - 1) μ :=
    (h_kl_int.add (integrable_exp_sub_cgf h_exp_int)).sub (integrable_const 1)
  have h_pointwise :
      (fun x => f x * (t * X x - c)) ≤
      fun x => InformationTheory.klFun (f x) + Real.exp (t * X x - c) - 1 := by
    intro x
    exact mul_le_klFun_add_exp_sub_one (hf_nonneg x)
  have h_integral_le :
      ∫ x, f x * (t * X x - c) ∂μ ≤
      ∫ x, InformationTheory.klFun (f x) + Real.exp (t * X x - c) - 1 ∂μ :=
    integral_mono h_left_int h_right_int h_pointwise
  -- Step 2: evaluate the left integral using `∫ f = 1`
  have h_left_eq :
      ∫ x, f x * (t * X x - c) ∂μ =
        t * ∫ x, f x * X x ∂μ - c := by
    calc
      ∫ x, f x * (t * X x - c) ∂μ =
          ∫ x, t * (f x * X x) - c * f x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = t * ∫ x, f x * X x ∂μ - c * ∫ x, f x ∂μ := by
        rw [integral_sub (hfX_int.const_mul t) (hf_int.const_mul c),
          integral_const_mul, integral_const_mul]
      _ = t * ∫ x, f x * X x ∂μ - c := by rw [h_integral, mul_one]
  -- Step 3: the tilted density integrates to `1`, so the right integral is `∫ klFun f`
  have h_right_eq :
      ∫ x, InformationTheory.klFun (f x) + Real.exp (t * X x - c) - 1 ∂μ =
        ∫ x, InformationTheory.klFun (f x) ∂μ := by
    have h_exp_sub_int :
        Integrable (fun x => Real.exp (t * X x - c)) μ := by
      simpa [c] using integrable_exp_sub_cgf (μ := μ) (X := X) (t := t) h_exp_int
    have h_exp_sub_eq_one :
        ∫ x, Real.exp (t * X x - c) ∂μ = 1 := by
      simpa [c] using integral_exp_sub_cgf_eq_one (μ := μ) (X := X) (t := t) h_exp_int
    calc
      ∫ x, InformationTheory.klFun (f x) + Real.exp (t * X x - c) - 1 ∂μ =
          (∫ x, InformationTheory.klFun (f x) ∂μ) +
            ∫ x, Real.exp (t * X x - c) ∂μ - ∫ _x : Ω, (1 : ℝ) ∂μ := by
        have hsub :=
          integral_sub (h_kl_int.add h_exp_sub_int) (integrable_const (1 : ℝ))
        have hadd := integral_add h_kl_int h_exp_sub_int
        have hadd' :
            ∫ a, ((fun x => InformationTheory.klFun (f x)) +
                fun x => Real.exp (t * X x - c)) a ∂μ =
              ∫ a, InformationTheory.klFun (f a) ∂μ +
                ∫ a, Real.exp (t * X a - c) ∂μ := by
          simpa [Pi.add_apply] using hadd
        rw [hadd'] at hsub
        simpa [Pi.add_apply, Pi.sub_apply] using hsub
      _ = ∫ x, InformationTheory.klFun (f x) ∂μ := by
        rw [h_exp_sub_eq_one, integral_const, probReal_univ]
        simp
  rw [h_left_eq, h_right_eq] at h_integral_le
  linarith
