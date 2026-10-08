import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.ProbabilityTheoryHasBernsteinMGF
import AFTD.Kb.ProbabilityStatistics.CenteredChiSquaredStep

/-!
# hasBernsteinMGF_centered_chi_squared

Topic: concentration   Node: 5b003e18ec4c

Provenance: helper lemma. TCSlib, `hasBernsteinMGF_centered_chi_squared`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bernstein MGF bound for a centered chi-squared summand. Fix an integer $k \ge 1$, and let $Y$ be a real-valued random variable on a probability
space $(\Omega, \mu)$ whose law is the centered Gaussian $\mathcal{N}(0, 1/k)$ of mean
$0$ and variance $1/k$. Then the centered square $Y^2 - 1/k$ satisfies the Bernstein MGF
condition on $(\Omega, \mu)$ with quadratic-growth parameter $c = 2/k^2$ and radius
$t_{\max} = k/4$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Bernstein MGF instance for the centered chi-squared summand.** For a measurable real random variable `Y` on a probability space with law `N(0, 1/k)` (`k > 0`), the centered square `Y² − 1/k` has a Bernstein-type MGF with parameters `(2/k², k/4)`: `exp(t(Y² − 1/k))` is integrable and its mean is at most `exp((2/k²) t²)` for `|t| ≤ k/4`. This is the sub-exponential property of a centered chi-squared summand, [Ver18, Lemma 2.7.6] (Gaussian case) with the explicit constants from [DG03, proof of Lemma 2.2]; it packages `centered_chi_squared_step` into the abstract Bernstein form so that the sum and tail-bound machinery in `TCSlib.LearningTheory.JohnsonLindenstrauss.Bernstein` applies uniformly to Gaussian, Rademacher, and other sub-Gaussian families. -/
theorem hasBernsteinMGF_centered_chi_squared
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ) (hk : 0 < k)
    (Y : Ω → ℝ) (hY_meas : Measurable Y)
    (hY_law : Measure.map Y μ = gaussianReal 0 ⟨1 / k, by positivity⟩) :
    HasBernsteinMGF (fun ω => (Y ω) ^ 2 - 1 / k) μ (2 / (k : ℝ) ^ 2) ((k : ℝ) / 4) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact (centered_chi_squared_step μ k hk Y hY_meas hY_law t ht).1
  · intro t ht
    have h := (centered_chi_squared_step μ k hk Y hY_meas hY_law t ht).2
    -- `mgf ≤ exp(2 t²/k²)`. Match `c = 2/k²`, so `c · t² = 2 t²/k²`. ✓
    convert h using 2
    ring
