import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.JointDistribution

/-!
# JointDistribution.rowMarginal

Topic: equilibria   Node: b0be344a5e99

Provenance: formalization of a published result. Source: TCSlib, `JointDistribution.rowMarginal`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The row marginal of $\sigma$ at row action $i$ is
$\sigma^{\mathrm{row}}_i = \sum_{j} \sigma_{ij}$,
i.e.\ the probability that the row player plays $i$ under $\sigma$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
variable {M N : ℕ} in
/-- The row marginal of a joint distribution: the probability that the row player plays `i`, i.e. the sum of the profile probabilities `(i, j)` over columns `j`. [Rou13-L13, Def. 3.4]. -/
noncomputable def JointDistribution.rowMarginal (σ : JointDistribution M N) (i : Fin M) : ℝ :=
  ∑ j : Fin N, σ.prob i j
