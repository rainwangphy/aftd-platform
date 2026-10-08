import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.ProbabilityTheoryHasBernsteinMGF
import AFTD.Kb.ProbabilityStatistics.ProbabilityTheoryHasBernsteinMGFMeasureAbsGtLe
import AFTD.Kb.ProbabilityStatistics.ProbabilityTheoryHasBernsteinMGFSumOfIIndepFun
import AFTD.Kb.ProbabilityStatistics.HasBernsteinMGFCenteredChiSquared

/-!
# chi_squared_tail

Topic: concentration   Node: f70e5e3ed80f

Provenance: helper lemma. TCSlib, `chi_squared_tail`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Chi-squared tail bound for independent $N(0,1/k)$ variables. Let $\mu$ be a probability measure on $\Omega$, let $k \ge 1$, and let $Y_1,\dots,Y_k :
\Omega \to \bbr$ be independent random variables, each with law $N(0, 1/k)$. Then for
every $\varepsilon$ with $0 < \varepsilon < 1$,
\[
  \mu\!\left\{\omega \;\middle|\; \varepsilon
    < \Bigl|\,\textstyle\sum_{i=1}^{k} Y_i(\omega)^2 - 1\Bigr|\right\}
  \;\le\; 2\exp\!\Bigl(-\tfrac{k\,\varepsilon^2}{8}\Bigr).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Chi-squared tail bound.** If `Y_1, …, Y_k` (`k > 0`) are mutually independent measurable real random variables on a probability space, each with law `N(0, 1/k)`, then for every `0 < ε < 1` the probability that `Σᵢ Yᵢ²` deviates from `1` by more than `ε` is at most `2·exp(−kε²/8)`. This is the concentration of a normalized chi-squared variable with `k` degrees of freedom, [DG03, Lemma 2.2], obtained here as an instance of Bernstein's inequality [Ver18, Thm 2.8.1]. Deviation from the source: DG03 prove the sharper one-sided bounds `exp(k/2 (1 − β + ln β))` for `‖Ax‖² ≤ β‖x‖²` and its mirror; we state the two-sided bound `2 exp(−kε²/8)`, obtained via the Bernstein parameters `(2/k², k/4)` of `hasBernsteinMGF_centered_chi_squared`. **Proof sketch.** Step 1: form the centered summands `S_i = Y_i² − 1/k`; they are measurable and mutually independent. Step 2: each `S_i` has a Bernstein-type MGF with parameters `(2/k², k/4)` by `hasBernsteinMGF_centered_chi_squared`. Step 3: by `HasBernsteinMGF.sum_of_iIndepFun` the sum `Σ S_i` has parameters `(2/k, k/4)`. Step 4: the bad event `{ε < |Σ Y_i² − 1|}` equals `{ε < |Σ S_i|}` since `Σ S_i = Σ Y_i² − 1`. Step 5: `ε < 1 = 2·(2/k)·(k/4)` puts `ε` in the admissible range, so the two-sided Bernstein bound `HasBernsteinMGF.measure_abs_gt_le` gives `2·exp(−ε²/(4·(2/k)))`. Step 6: the exponent `−ε²/(8/k)` equals `−kε²/8`. -/
lemma chi_squared_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hk_pos : 0 < k)
    (Y : Fin k → Ω → ℝ)
    (hY_meas : ∀ i, Measurable (Y i))
    (hY_law : ∀ i, Measure.map (Y i) μ =
      gaussianReal 0 ⟨1 / k, by positivity⟩)
    (hY_indep : iIndepFun Y μ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (μ {ω | ε < |(∑ i, (Y i ω) ^ 2) - 1|}).toReal ≤
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by
  -- Route through the abstract Bernstein concentration in
  -- `TCSlib.LearningTheory.JohnsonLindenstrauss.Bernstein`. The Gaussian-specific step is
  -- `centered_chi_squared_step` (packaged as `hasBernsteinMGF_centered_chi_squared`);
  -- everything else is generic Bernstein/Chernoff bookkeeping.
  classical
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  have hk_ne_zero : (k : ℝ) ≠ 0 := hk_real_pos.ne'
  -- Step 1: centered chi-squared summands `S i := Y_i² − 1/k`.
  set S : Fin k → Ω → ℝ := fun i ω => (Y i ω) ^ 2 - 1 / k with hS_def
  have hS_meas : ∀ i, Measurable (S i) := fun i =>
    ((hY_meas i).pow_const 2).sub measurable_const
  have hS_indep : iIndepFun S μ :=
    hY_indep.comp (fun _ y => y ^ 2 - 1 / (k : ℝ)) (fun _ => by fun_prop)
  -- Step 2: each `S i` has Bernstein MGF `(2/k², k/4)` via the Gaussian step.
  have hS_bern : ∀ i, HasBernsteinMGF (S i) μ (2 / (k : ℝ) ^ 2) ((k : ℝ) / 4) :=
    fun i => hasBernsteinMGF_centered_chi_squared μ k hk_pos (Y i) (hY_meas i) (hY_law i)
  -- Step 3: sum has Bernstein MGF `(k · 2/k², k/4) = (2/k, k/4)` by closure under
  -- independent sums.
  have hSum_bern : HasBernsteinMGF (fun ω => ∑ i, S i ω) μ
      (2 / (k : ℝ)) ((k : ℝ) / 4) := by
    have h := HasBernsteinMGF.sum_of_iIndepFun hS_indep hS_meas
      (s := Finset.univ) (fun i _ => hS_bern i)
    -- ∑ i ∈ univ, 2/k² = k · 2/k² = 2/k.
    convert h using 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- Step 4: bad event reduces: `ε < |Σ Y_i² − 1|  ⇔  ε < |Σ S_i|`.
  have hsum_S : ∀ ω, ∑ i, S i ω = (∑ i, (Y i ω) ^ 2) - 1 := by
    intro ω
    simp only [S, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hbad_eq : {ω | ε < |(∑ i, (Y i ω) ^ 2) - 1|}
      = {ω | ε < |∑ i, S i ω|} := by
    ext ω; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsum_S]
  rw [hbad_eq]
  -- Step 5: apply abstract Bernstein concentration (`measure_abs_gt_le`).
  -- Range: `2 · (2/k) · (k/4) = 1`, and `ε < 1`, so we're in range.
  have h2c_pos : 0 < 2 / (k : ℝ) := by positivity
  have hε_le_range : ε ≤ 2 * (2 / (k : ℝ)) * ((k : ℝ) / 4) := by
    have : 2 * (2 / (k : ℝ)) * ((k : ℝ) / 4) = 1 := by field_simp; norm_num
    rw [this]; linarith
  have h_concentration := hSum_bern.measure_abs_gt_le h2c_pos ε hε_pos.le hε_le_range
  -- Step 6: the exponent: `-ε² / (4 · 2/k) = -kε² / 8`.
  refine le_trans h_concentration ?_
  apply le_of_eq
  congr 2
  field_simp
  ring
