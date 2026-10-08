import AFTD.Prelude

/-!
# BadSingle

Topic: concentration   Node: 5266ad738ade

Provenance: formalization of a published result. Source: TCSlib, `BadSingle`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a parameter $\varepsilon\in\mathbb{R}$, a matrix $A$, and a vector
$x\in\mathbb{R}^d$, the predicate $\texttt{BadSingle}\,\varepsilon\,A\,x$ holds when
the squared-norm distortion is strictly too large:
\[
  \varepsilon \|x\|^2 < \bigl|\,\|Ax\|^2 - \|x\|^2\,\bigr|.
\]
This is the ``bad event'' whose probability must be controlled by the JL
concentration argument.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- The "bad event" for a single vector `x` under the random projection `A`: the squared norm of `Ax` differs from the squared norm of `x` by strictly more than `ε‖x‖²`, that is, `ε‖x‖² < |‖Ax‖² − ‖x‖²|`. This is the failure event of [DG03, Lemma 2.2] (the event `|‖Ax‖² − ‖x‖²| > ε‖x‖²`), stated with strict inequality. -/
noncomputable def BadSingle (ε : ℝ) (A : Matrix (Fin k) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  ε * ‖x‖ ^ 2 < |‖A.toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2|
