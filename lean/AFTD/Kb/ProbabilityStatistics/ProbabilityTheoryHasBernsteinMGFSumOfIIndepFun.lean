import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.ProbabilityTheoryHasBernsteinMGF

/-!
# ProbabilityTheory.HasBernsteinMGF.sum_of_iIndepFun

Topic: concentration   Node: bb0b6afbeb45

Provenance: helper lemma. TCSlib, `ProbabilityTheory.HasBernsteinMGF.sum_of_iIndepFun`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/Bernstein.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Sub-exponential MGF bound for independent sums. Let $(X_i)_{i \in \iota}$ be a family of measurable real random variables on a
probability space $(\Omega, \mu)$ that are mutually independent, and let $s$ be a finite
set of indices. Fix a radius $t_{\max}$, and suppose that for each $i \in s$ there is a
constant $c_i$ such that $e^{tX_i}$ is $\mu$-integrable and $\mathbf{E}_\mu[e^{tX_i}]
\le e^{c_i t^2}$ for every $t$ with $|t| \le t_{\max}$. Then the sum $\sum_{i \in s}
X_i$ satisfies the same two-parameter sub-exponential bound with radius $t_{\max}$ and
constant $\sum_{i \in s} c_i$: for every $t$ with $|t| \le t_{\max}$, the moment $e^{t
\sum_{i \in s} X_i}$ is $\mu$-integrable and $\mathbf{E}_\mu\!\left[e^{t \sum_{i \in s}
X_i}\right] \le e^{(\sum_{i \in s} c_i)\, t^2}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real in
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} in
variable {X : Ω → ℝ} {μ : Measure Ω} {c tmax : ℝ} in
/-- **Closure under independent sums.** If `X i` (`i` ranging over a finite set `s`) is a family of mutually independent measurable real random variables on a probability space, and each `X i` has a Bernstein-type MGF with parameters `(c i, tmax)` for a common radius `tmax`, then the sum `∑ i ∈ s, X i` has a Bernstein-type MGF with parameters `(∑ i ∈ s, c i, tmax)`. This is the MGF-of-a-sum step in [Ver18, proof of Thm 2.8.1]. Only independence is assumed, not identical distribution. **Proof sketch.** Step 1: integrability of `exp(t·∑ X i)` for `|t| ≤ tmax` follows from the per-summand integrability via independence (Mathlib's `iIndepFun.integrable_exp_mul_sum`). Step 2: by independence the moment generating function of the sum at `t` is the product of the individual ones; bound each factor by `exp(c i · t²)` and collect the product of exponentials into `exp((∑ c i)·t²)`. -/
lemma ProbabilityTheory.HasBernsteinMGF.sum_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    {c : ι → ℝ} {tmax : ℝ}
    {s : Finset ι} (h_bern : ∀ i ∈ s, HasBernsteinMGF (X i) μ (c i) tmax) :
    HasBernsteinMGF (fun ω => ∑ i ∈ s, X i ω) μ (∑ i ∈ s, c i) tmax := by
  refine ⟨?_, ?_⟩
  · -- Step 1: integrability of `exp(t · ∑ X_i)` on `|t| ≤ tmax` from per-element
    -- integrability.
    intro t ht
    have h1 : Integrable (fun ω => Real.exp (t * (∑ i ∈ s, X i) ω)) μ := by
      refine h_indep.integrable_exp_mul_sum h_meas (fun i hi => ?_)
      exact (h_bern i hi).integrable t ht
    convert h1 using 1
    funext ω
    rw [Finset.sum_apply]
  · -- Step 2: MGF bound:
    -- `mgf (∑ X_i) μ t = ∏ mgf (X_i) μ t ≤ ∏ exp(c_i t²) = exp(∑ c_i · t²)`.
    intro t ht
    have h_pi_eq : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
      funext ω; rw [Finset.sum_apply]
    rw [h_pi_eq, h_indep.mgf_sum h_meas]
    calc ∏ i ∈ s, mgf (X i) μ t
        ≤ ∏ i ∈ s, Real.exp (c i * t ^ 2) := by
          apply Finset.prod_le_prod
          · exact fun i _ => mgf_nonneg
          · exact fun i hi => (h_bern i hi).mgf_le t ht
      _ = Real.exp ((∑ i ∈ s, c i) * t ^ 2) := by
          rw [← Real.exp_sum, Finset.sum_mul]
