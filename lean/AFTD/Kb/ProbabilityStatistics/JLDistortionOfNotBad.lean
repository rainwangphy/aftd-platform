import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.BadSingle
import AFTD.Kb.ProbabilityStatistics.JLDistortion

/-!
# JLDistortion.of_not_bad

Topic: concentration   Node: e9756a7d57c0

Provenance: helper lemma. TCSlib, `JLDistortion.of_not_bad`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/UnionBound.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Distortion bound from a controlled single-vector event. Let $\varepsilon \in \bbr$, let $u, v \in \bbr^d$, and let $A$ be a real $k \times d$
matrix, acting as a linear map $\bbr^d \to \bbr^k$. Suppose the difference $u - v$ does
not trigger the bad distortion event for $A$; that is, the squared-norm distortion of
$u-v$ stays within the allowed band,
\[
  \bigl|\,\norm{A(u-v)}^2 - \norm{u-v}^2\,\bigr| \;\le\; \varepsilon\,\norm{u-v}^2 .
\]
Then the images $Au$ and $Av$ satisfy the two-sided single-pair distortion bound
\[
(1 - \varepsilon)\,\norm{u - v}^2 \;\le\; \norm{Au - Av}^2 \;\le\; (1 +
\varepsilon)\,\norm{u - v}^2 .
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- If the matrix `A` does not distort the difference vector `u − v` by more than a factor `ε` (the negation of `BadSingle ε A (u − v)`), then the pair `(u, v)` satisfies the `(1 ± ε)` distortion bound `JLDistortion` under `A`. -/
lemma JLDistortion.of_not_bad (ε : ℝ) (u v : EuclideanSpace ℝ (Fin d))
    (A : Matrix (Fin k) (Fin d) ℝ)
    (h : ¬ BadSingle ε A (u - v)) :
    JLDistortion ε u v (A.toEuclideanLin u) (A.toEuclideanLin v) := by
  -- `BadSingle ε A (u-v)` says `ε ‖u-v‖² < |‖A(u-v)‖² - ‖u-v‖²|`.
  -- Its negation plus `A.toEuclideanLin (u-v) = A.toEuclideanLin u - A.toEuclideanLin v`
  -- gives both sides of `JLDistortion`.
  unfold BadSingle at h
  push_neg at h
  rw [map_sub] at *
  refine ⟨?_, ?_⟩
  · -- (1 - ε) ‖u-v‖² ≤ ‖A(u-v)‖²
    have := abs_le.mp h
    have h1 := sq_nonneg ‖u - v‖
    have h2 := sq_nonneg ‖A.toEuclideanLin u - A.toEuclideanLin v‖
    linarith [this.1, this.2]
  · -- ‖A(u-v)‖² ≤ (1 + ε) ‖u-v‖²
    have := abs_le.mp h
    linarith [this.1, this.2]
