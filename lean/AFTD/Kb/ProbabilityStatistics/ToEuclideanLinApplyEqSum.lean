import AFTD.Prelude

/-!
# toEuclideanLin_apply_eq_sum

Topic: concentration   Node: 648a999b3679

Provenance: helper lemma. TCSlib, `toEuclideanLin_apply_eq_sum`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Coordinates of a matrix-vector product. Let $A\in\bbr^{k\times d}$ be a $k\times d$ real matrix, regarded as the linear map from
the Euclidean space $\bbr^{d}$ to $\bbr^{k}$ that it induces, and let $x\in\bbr^{d}$.
Then for each index $i\in\{1,\dots,k\}$, the $i$-th coordinate of the image $Ax$ is
given by
\[
  (Ax)_i \;=\; \sum_{j} A_{ij}\,x_j .
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- The `i`-th coordinate of the image of `x` under the linear map of the matrix `A` is the row sum `∑ j, A i j * x j`; this holds by definition of `Matrix.toEuclideanLin`. -/
lemma toEuclideanLin_apply_eq_sum
    (A : Matrix (Fin k) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    (A.toEuclideanLin x) i = ∑ j, A i j * x j := rfl
