import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityVariationalIntegralMulLeIntegralKlFunAddCgf

/-!
# CommunicationComplexity.half_integral_abs_sub_one_sq_le_integral_klFun

Topic: information   Node: 07a6264d72b8

Provenance: helper lemma. TCSlib, `CommunicationComplexity.half_integral_abs_sub_one_sq_le_integral_klFun`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A Pinsker-type inequality for the Kullback–Leibler generator. Let $(\Omega, \mu)$ be a probability space, and let $\varphi(t) = t \log t - t + 1$ for
$t \ge 0$ denote the convex generator of the Kullback–Leibler divergence. Let $f :
\Omega \to \bbr$ be a measurable, integrable, nonnegative function with $\int_\Omega f
\, d\mu = 1$, so that $f$ is the density of a probability measure with respect to $\mu$,
and assume that $x \mapsto \varphi(f(x))$ is integrable with respect to $\mu$. Then
\[
\tfrac{1}{2}\Bigl(\int_\Omega \abs{f(x) - 1}\, d\mu\Bigr)^{2} \;\le\; \int_\Omega
\varphi(f(x))\, d\mu .
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- The density form of Pinsker's inequality: for a measurable nonnegative density `f` with `∫ f dμ = 1` and `klFun ∘ f` integrable, `½ (∫ |f − 1| dμ)² ≤ ∫ klFun (f) dμ`. **Proof sketch.** Let `s = sign (f − 1)` (with value `1` where `f ≥ 1`), `m = ∫ s dμ`, `X = s − m` and `L = ∫ |f − 1| dμ`. Step 1: `X` is measurable, centred, and takes values in the interval `[−1 − m, 1 − m]` of length `2`, so by Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) it is sub-Gaussian and `cgf_X(t) ≤ t²/2`; in particular `exp (t X)` is integrable. Step 2: `∫ f X dμ = L`: since `|f − 1| = (f − 1) s` pointwise, `∫ f X = ∫ (f − 1) s + ∫ s − m ∫ (f − 1) − m = L + m − 0 − m`. Step 3: apply the variational inequality `variational_integral_mul_le_integral_klFun_add_cgf` with `t = L` to get `L² ≤ ∫ klFun f + cgf_X(L) ≤ ∫ klFun f + L²/2`, and rearrange. -/
theorem CommunicationComplexity.half_integral_abs_sub_one_sq_le_integral_klFun
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf_meas : Measurable f) (hf_int : Integrable f μ)
    (h_kl_int : Integrable (fun x => InformationTheory.klFun (f x)) μ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (h_integral : ∫ x, f x ∂μ = 1) :
    (1 / 2 : ℝ) * (∫ x, |f x - 1| ∂μ) ^ 2 ≤
      ∫ x, InformationTheory.klFun (f x) ∂μ := by
  let s : Ω → ℝ := fun x => if 0 ≤ f x - 1 then 1 else -1
  let m : ℝ := ∫ x, s x ∂μ
  let X : Ω → ℝ := fun x => s x - m
  let L : ℝ := ∫ x, |f x - 1| ∂μ
  -- Step 1: the centred sign variable `X` is bounded and centred, hence sub-Gaussian
  have hset : MeasurableSet {x | 0 ≤ f x - 1} :=
    measurableSet_Ici.preimage (hf_meas.sub measurable_const)
  have hs_meas : Measurable s := by
    dsimp [s]
    exact Measurable.ite hset measurable_const measurable_const
  have hs_bound : ∀ᵐ x ∂μ, s x ∈ Set.Icc (-1 : ℝ) 1 := by
    refine ae_of_all μ ?_
    intro x
    by_cases hx : 1 ≤ f x <;> simp [s, sub_nonneg, hx]
  have hs_int : Integrable s μ :=
    Integrable.of_mem_Icc (-1 : ℝ) 1 hs_meas.aemeasurable hs_bound
  have hX_meas : Measurable X := hs_meas.sub measurable_const
  have hX_integral_zero : μ[X] = 0 := by
    dsimp [X, m]
    rw [integral_sub hs_int (integrable_const _), integral_const, probReal_univ]
    simp
  have hX_mem_Icc :
      ∀ᵐ x ∂μ, X x ∈ Set.Icc ((-1 : ℝ) - m) (1 - m) := by
    refine ae_of_all μ ?_
    intro x
    by_cases hx : 1 ≤ f x
    · simp [X, s, sub_nonneg, hx]
    · simp [X, s, sub_nonneg, hx]
  have hX_subG :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (μ := μ) (X := X) (a := (-1 : ℝ) - m) (b := 1 - m)
      hX_meas.aemeasurable hX_mem_Icc hX_integral_zero
  have hX_norm_bound : ∀ᵐ x ∂μ, ‖X x‖ ≤ |m| + 1 := by
    refine ae_of_all μ ?_
    intro x
    have hs_abs : |s x| ≤ (1 : ℝ) := by
      by_cases hx : 1 ≤ f x <;> simp [s, sub_nonneg, hx]
    calc
      ‖X x‖ = |s x - m| := rfl
      _ ≤ |s x| + |m| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (s x) (-m)
      _ ≤ |m| + 1 := by linarith
  have hfX_int : Integrable (fun x => f x * X x) μ :=
    (hf_int.bdd_mul hX_meas.aestronglyMeasurable hX_norm_bound).congr
      (Filter.Eventually.of_forall (fun x => mul_comm (X x) (f x)))
  -- Step 2: `∫ f X = L`, the `L¹` distance of `f` from `1`
  have h_abs_int : Integrable (fun x => |f x - 1|) μ :=
    (hf_int.sub (integrable_const 1)).abs
  have h_sub_integral_zero : ∫ x, f x - 1 ∂μ = 0 := by
    rw [integral_sub hf_int (integrable_const 1), h_integral, integral_const, probReal_univ]
    simp
  have h_abs_eq_signed : L = ∫ x, (f x - 1) * s x ∂μ := by
    dsimp [L, s]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : 0 ≤ f x - 1
    · simp [hx, abs_of_nonneg hx]
    · have hx' : f x - 1 ≤ 0 := le_of_not_ge hx
      simp [hx, abs_of_nonpos hx']
  have h_signed_int : Integrable (fun x => (f x - 1) * s x) μ := by
    have hs_norm_bound : ∀ᵐ x ∂μ, ‖s x‖ ≤ (1 : ℝ) := by
      filter_upwards [hs_bound] with x hx
      rw [Real.norm_eq_abs]
      exact abs_le.2 hx
    exact ((hf_int.sub (integrable_const 1)).bdd_mul hs_meas.aestronglyMeasurable hs_norm_bound).congr
      (Filter.Eventually.of_forall (fun x => mul_comm (s x) (f x - 1)))
  have h_signed_integral_zero :
      ∫ x, (f x - 1) * m ∂μ = 0 := by
    rw [integral_mul_const, h_sub_integral_zero, zero_mul]
  have h_fX_eq_L : ∫ x, f x * X x ∂μ = L := by
    calc
      ∫ x, f x * X x ∂μ =
          ∫ x, (f x - 1) * s x + s x - (f x - 1) * m - m ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [X]
        ring
      _ = ∫ x, (f x - 1) * s x ∂μ + ∫ x, s x ∂μ -
          ∫ x, (f x - 1) * m ∂μ - ∫ _x : Ω, m ∂μ := by
        rw [integral_sub, integral_sub, integral_add]
        · exact h_signed_int
        · exact hs_int
        · exact h_signed_int.add hs_int
        · exact (hf_int.sub (integrable_const 1)).mul_const m
        · exact (h_signed_int.add hs_int).sub ((hf_int.sub (integrable_const 1)).mul_const m)
        · exact integrable_const m
      _ = L := by
        rw [← h_abs_eq_signed, h_signed_integral_zero, integral_const, probReal_univ]
        simp [m]
  -- Step 3: Hoeffding bound on the cgf and the variational inequality at `t = L`
  have h_cgf :
      ProbabilityTheory.cgf X μ L ≤ L ^ 2 / 2 := by
    have h := hX_subG.cgf_le L
    norm_num [Real.norm_eq_abs] at h
    simpa using h
  have h_var :=
    variational_integral_mul_le_integral_klFun_add_cgf
      (μ := μ) (f := f) (X := X) (t := L)
      hf_int h_kl_int hf_nonneg h_integral (hX_subG.integrable_exp_mul L) hfX_int
  have h_var' :
      L ^ 2 ≤ ∫ x, InformationTheory.klFun (f x) ∂μ + ProbabilityTheory.cgf X μ L := by
    rw [h_fX_eq_L] at h_var
    simpa [sq] using h_var
  nlinarith
