import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.JLDistortion

/-!
# IsJLEmbedding

Topic: concentration   Node: 45238fa0e994

Provenance: formalization of a published result. Source: TCSlib, `IsJLEmbedding`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/UnionBound.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A linear map $f : \mathbb{R}^d \to_L[\mathbb{R}] \mathbb{R}^k$ is an
\emph{$\varepsilon$-JL embedding} of a finite set $V$ if, for every ordered
pair $(u, v) \in V \times V$, the pair $(f(u), f(v))$ satisfies
\texttt{JLDistortion} $\varepsilon\; u\; v$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- A linear map `f : ℝ^d → ℝ^k` is an **ε-JL embedding** of the finite set `V` if it preserves all pairwise squared distances up to factor `(1 ± ε)`, i.e. `JLDistortion ε u v (f u) (f v)` for all `u, v ∈ V` [DG03, Thm 2.1]; origin [JL84]. Deviation: only linear maps are considered, and distances are squared. -/
noncomputable def IsJLEmbedding (ε : ℝ) (V : Finset (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) : Prop :=
  ∀ u ∈ V, ∀ v ∈ V, JLDistortion ε u v (f u) (f v)

-- `BadSingle` is defined in `JohnsonLindenstrauss.RowDistribution`; re-exported here.
