import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.JlConcentrationSingleViaChiSquared
import AFTD.Kb.ProbabilityStatistics.BadSingle
import AFTD.Kb.ProbabilityStatistics.InstMeasurableSpaceMatrixFinRealTCSlib
import AFTD.Kb.ProbabilityStatistics.ChiSquaredTail
import AFTD.Kb.ProbabilityStatistics.CenteredChiSquaredStep

/-!
# jl_concentration_single

Topic: concentration   Node: c9fa8f45020a

Provenance: helper lemma. TCSlib, `jl_concentration_single`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/UnionBound.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Johnson–Lindenstrauss concentration for a single vector. Let $k \ge 1$ and let $A$ be a random $k \times d$ matrix whose entries $A_{ij}$ are
independent Gaussian random variables, each distributed as $\mathcal{N}(0, 1/k)$. Then
for every fixed vector $x \in \bbr^d$ and every $\varepsilon$ with $0 < \varepsilon <
1$, the probability that $A$ distorts the squared norm of $x$ by more than a factor
$\varepsilon$ satisfies
\[
  \bbP\!\left[\, \bigl|\,\|Ax\|^2 - \|x\|^2\,\bigr| > \varepsilon\,\|x\|^2 \,\right]
  \;\le\; 2\,\exp\!\left(-\frac{k\,\varepsilon^2}{8}\right).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **JL concentration (single vector)** [DG03, Lemma 2.2]. If `A_ij ~ N(0, 1/k)` are i.i.d. Gaussian (with rows mutually independent and entries iid within each row), then for any fixed `x : ℝ^d` and any `0 < ε < 1`, `ℙ[ |‖Ax‖² − ‖x‖²| > ε · ‖x‖² ] ≤ 2 · exp(−k ε² / 8).` Deviation: the two-sided bound `2 exp(−kε²/8)` replaces the source's `exp(k/2 (1 − β + ln β))` tails (see `chi_squared_tail`). This is a wrapper around `jl_concentration_single_via_chi_squared` from `JohnsonLindenstrauss.ConcentrationBound`, fully proved (no axioms) via `centered_chi_squared_step` + a Bernstein/Chernoff argument. -/
theorem jl_concentration_single (hk_pos : 0 < k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (hA_meas : Measurable A)
    (hA_law : ∀ (i : Fin k) (j : Fin d),
      Measure.map (fun ω => A ω i j) μ =
        gaussianReal 0 ⟨1 / k, by positivity⟩)
    (hRowEntryIndep : ∀ i : Fin k, iIndepFun (fun (j : Fin d) ω => A ω i j) μ)
    (hRowsIndep : iIndepFun (fun (i : Fin k) (ω : Ω) (j : Fin d) => A ω i j) μ)
    (x : EuclideanSpace ℝ (Fin d))
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (μ {ω | BadSingle ε (A ω) x}).toReal ≤
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) :=
  jl_concentration_single_via_chi_squared hk_pos μ A hA_meas hA_law
    hRowEntryIndep hRowsIndep x ε hε_pos hε_lt
