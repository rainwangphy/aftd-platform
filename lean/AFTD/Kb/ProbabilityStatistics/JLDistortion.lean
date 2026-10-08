import AFTD.Prelude

/-!
# JLDistortion

Topic: concentration   Node: 0e827863b9c2

Provenance: formalization of a published result. Source: TCSlib, `JLDistortion`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/UnionBound.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For $\varepsilon \in \mathbb{R}$, vectors $u, v \in \mathbb{R}^d$, and their
images $u', v' \in \mathbb{R}^k$, \texttt{JLDistortion} asserts the two-sided
squared-distance inequality
\[
  (1 - \varepsilon)\,\|u - v\|^2 \;\le\; \|u' - v'\|^2 \;\le\;
  (1 + \varepsilon)\,\|u - v\|^2.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- The `(1 ± ε)` two-sided distortion bound for a single pair of points: the squared distance between the images `u'`, `v'` lies between `(1 − ε)` and `(1 + ε)` times the squared distance between `u` and `v` [DG03, Thm 2.1]; origin [JL84]. Deviation: stated for squared distances (the distance form is recovered in `JohnsonLindenstrauss.Main`). -/
noncomputable def JLDistortion (ε : ℝ) (u v : EuclideanSpace ℝ (Fin d))
    (u' v' : EuclideanSpace ℝ (Fin k)) : Prop :=
  (1 - ε) * ‖u - v‖ ^ 2 ≤ ‖u' - v'‖ ^ 2 ∧
  ‖u' - v'‖ ^ 2 ≤ (1 + ε) * ‖u - v‖ ^ 2
