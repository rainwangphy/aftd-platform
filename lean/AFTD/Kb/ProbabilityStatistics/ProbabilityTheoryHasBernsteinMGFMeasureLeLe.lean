import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.ProbabilityTheoryHasBernsteinMGF

/-!
# ProbabilityTheory.HasBernsteinMGF.measure_le_le

Topic: concentration   Node: 2dd6862af66c

Provenance: helper lemma. TCSlib, `ProbabilityTheory.HasBernsteinMGF.measure_le_le`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/Bernstein.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lower-tail Bernstein bound. Let $X : \Omega \to \bbr$ be a random variable on a probability space carrying a finite
measure $\mu$, and suppose $X$ satisfies the Bernstein moment generating function
condition with parameters $c$ and $t_{\max}$: for every $t$ with $|t| \le t_{\max}$, the
exponential moment $e^{tX}$ is $\mu$-integrable and $\E_\mu[e^{tX}] \le e^{c t^2}$. If
$c > 0$, then for every $s$ with $0 \le s \le 2 c\, t_{\max}$,
\[
\mu\bigl(\{\omega \mid X(\omega) \le -s\}\bigr) \;\le\;
\exp\!\Bigl(-\frac{s^2}{4c}\Bigr).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real in
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} in
variable {X : Ω → ℝ} {μ : Measure Ω} {c tmax : ℝ} in
/-- **Lower-tail Bernstein bound** by symmetry. If `X` has a Bernstein-type MGF with parameters `(c, tmax)` under a finite measure `μ`, `c > 0`, and `0 ≤ s ≤ 2c·tmax`, then the measure of the event `{X ≤ −s}` is at most `exp(−s²/(4c))`. This is the Chernoff step of [Ver18, proof of Thm 2.8.1] applied to `−X`; the same single-parameter deviation as in `measure_ge_le` applies. **Proof sketch.** Step 1: take `t = −s/(2c)`; the hypotheses give `−tmax ≤ t ≤ 0`, so the MGF bound applies at `t`. Step 2 (Chernoff, lower tail): the measure of `{X ≤ −s}` is at most `exp(−t·(−s))` times the MGF of `X` at `t` (Mathlib's `measure_le_le_exp_mul_mgf`), which is at most `exp(−t·(−s) + c·t²)`. Step 3: at this `t` the exponent equals `−s²/(4c)` exactly. -/
lemma ProbabilityTheory.HasBernsteinMGF.measure_le_le {μ : Measure Ω} [IsFiniteMeasure μ]
    (h : HasBernsteinMGF X μ c tmax)
    (hc : 0 < c) (s : ℝ) (hs_pos : 0 ≤ s) (hs_le : s ≤ 2 * c * tmax) :
    (μ {ω | X ω ≤ -s}).toReal ≤ Real.exp (-s ^ 2 / (4 * c)) := by
  -- Step 1: use t = -s/(2c), which lies in `[-tmax, 0]`.
  set t : ℝ := -(s / (2 * c)) with ht_def
  have h2c_pos : 0 < 2 * c := by linarith
  have ht_neg : t ≤ 0 := by rw [ht_def]; linarith [div_nonneg hs_pos h2c_pos.le]
  have ht_le_tmax : -t ≤ tmax := by
    rw [ht_def]; simp only [neg_neg]; rw [div_le_iff₀ h2c_pos]; linarith
  have ht_abs : |t| ≤ tmax := by rw [abs_of_nonpos ht_neg]; exact ht_le_tmax
  -- Step 2: Chernoff (lower tail) via `measure_le_le_exp_mul_mgf`.
  have h_chernoff : (μ {ω | X ω ≤ -s}).toReal ≤
      Real.exp (-t * (-s)) * mgf X μ t :=
    measure_le_le_exp_mul_mgf (-s) ht_neg (h.integrable t ht_abs)
  refine le_trans h_chernoff ?_
  refine le_trans (mul_le_mul_of_nonneg_left (h.mgf_le t ht_abs) (Real.exp_pos _).le) ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- Step 3: at the optimal `t = -s/(2c)` the exponent is exactly `-s²/(4c)`.
  have h_exponent : -t * (-s) + c * t ^ 2 = -s ^ 2 / (4 * c) := by
    rw [ht_def]
    field_simp
    ring
  exact h_exponent.le
