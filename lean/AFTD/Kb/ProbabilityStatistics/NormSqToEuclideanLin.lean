import AFTD.Prelude

/-!
# norm_sq_toEuclideanLin

Topic: concentration   Node: d456df1ce8ed

Provenance: helper lemma. TCSlib, `norm_sq_toEuclideanLin`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Squared Euclidean norm as a sum of squared coordinates. Let $A$ be a $k \times d$ real matrix, regarded as the linear map $x \mapsto Ax$ from
the Euclidean space $\bbr^d$ to $\bbr^k$, and let $x \in \bbr^d$. Then the squared
Euclidean norm of the image is the sum of the squares of its coordinates,
\[
  \norm{Ax}^2 = \sum_{i=1}^{k} (Ax)_i^2 .
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- The squared Euclidean norm of the image of `x` under the linear map of the matrix `A` equals the sum over the rows `i` of the squared coordinates `((A.toEuclideanLin x) i)²`. -/
lemma norm_sq_toEuclideanLin
    (A : Matrix (Fin k) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖A.toEuclideanLin x‖ ^ 2 = ∑ i, ((A.toEuclideanLin x) i) ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (by positivity)]
  simp [sq_abs]
