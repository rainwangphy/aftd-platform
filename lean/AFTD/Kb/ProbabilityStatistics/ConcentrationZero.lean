import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.BadSingle

/-!
# concentration_zero

Topic: concentration   Node: 39bc8133b983

Provenance: helper lemma. TCSlib, `concentration_zero`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Concentration bound at the zero vector. Let $\mu$ be a probability measure on a measurable space $\Omega$, let $\omega \mapsto
A(\omega)$ be a family of $k \times d$ real matrices indexed by $\Omega$, and let
$\varepsilon \in \bbr$. Then the probability that the zero vector $0 \in \bbr^d$
triggers the bad distortion event, namely that
\[
  \varepsilon\,\|0\|^2 < \bigl|\,\|A(\omega)\,0\|^2 - \|0\|^2\,\bigr|,
\]
satisfies
\[
\mu\bigl\{\omega : \varepsilon\,\|0\|^2 < \bigl|\,\|A(\omega)\,0\|^2 -
\|0\|^2\,\bigr|\bigr\}
    \;\le\; 2\exp\!\Bigl(-\tfrac{k\,\varepsilon^2}{8}\Bigr).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- For the zero vector the single-vector concentration bound holds trivially: for any random matrix `A` and any `ε`, the probability of the bad event `BadSingle ε (A ω) 0` is at most `2·exp(−kε²/8)`, because that event is empty. -/
lemma concentration_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (ε : ℝ) :
    (μ {ω | BadSingle ε (A ω) (0 : EuclideanSpace ℝ (Fin d))}).toReal ≤
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by
  have hempty : {ω | BadSingle ε (A ω) (0 : EuclideanSpace ℝ (Fin d))} = ∅ := by
    ext ω
    simp only [BadSingle, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_lt]
    simp [map_zero]
  rw [hempty, measure_empty, ENNReal.toReal_zero]
  positivity
