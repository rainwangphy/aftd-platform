import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.JLDistortion
import AFTD.Kb.Tcs.V

/-!
# BadPair

Topic: concentration   Node: d0636cd4f7d0

Provenance: formalization of a published result. Source: TCSlib, `BadPair`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/UnionBound.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a $k \times d$ matrix $A$ and a finite set
$V \subseteq \mathbb{R}^d$, \texttt{BadPair} $\varepsilon\; V\; A$ holds when
there exists some ordered pair $(u, v) \in V \times V$ whose images under $A$
fail the distortion predicate, i.e.\ the projection distorts that pair by
more than a factor of $\varepsilon$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- The "bad event" for the whole set `V` under the matrix `A`: some ordered pair `(u, v) ∈ V × V` fails the `(1 ± ε)` distortion bound `JLDistortion` under `A` [DG03, proof of Thm 2.1]. -/
noncomputable def BadPair (ε : ℝ) (V : Finset (EuclideanSpace ℝ (Fin d)))
    (A : Matrix (Fin k) (Fin d) ℝ) : Prop :=
  ∃ u ∈ V, ∃ v ∈ V, ¬ JLDistortion ε u v
    (A.toEuclideanLin u) (A.toEuclideanLin v)
