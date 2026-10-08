import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.JointDistribution

/-!
# JointDistribution.colMarginal

Topic: equilibria   Node: f2cc9d163602

Provenance: formalization of a published result. Source: TCSlib, `JointDistribution.colMarginal`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The column marginal of $\sigma$ at column action $j$ is
$\sigma^{\mathrm{col}}_j = \sum_{i} \sigma_{ij}$,
i.e.\ the probability that the column player plays $j$ under $\sigma$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
variable {M N : ℕ} in
/-- The column marginal of a joint distribution: the probability that the column player plays `j`, i.e. the sum of the profile probabilities `(i, j)` over rows `i`. [Rou13-L13, Def. 3.4]. -/
noncomputable def JointDistribution.colMarginal (σ : JointDistribution M N) (j : Fin N) : ℝ :=
  ∑ i : Fin M, σ.prob i j
