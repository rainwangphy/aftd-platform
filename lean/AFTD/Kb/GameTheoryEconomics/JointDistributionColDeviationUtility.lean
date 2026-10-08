import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Game
import AFTD.Kb.GameTheoryEconomics.JointDistribution
import AFTD.Kb.GameTheoryEconomics.JointDistributionRowMarginal

/-!
# JointDistribution.colDeviationUtility

Topic: equilibria   Node: 151cffc889a0

Provenance: formalization of a published result. Source: TCSlib, `JointDistribution.colDeviationUtility`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The column player's expected utility from unilaterally deviating to the fixed
pure action $j'$, while the row player keeps $\sigma$'s row marginal:
$\sum_{i} \sigma^{\mathrm{row}}_i \cdot u_c(i, j')$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
variable {M N : ℕ} in
/-- The column player's expected utility from unilaterally deviating to the pure action `j'` while the row player's action is still drawn from `σ`'s row marginal. [Rou13-L13, §3]. -/
noncomputable def JointDistribution.colDeviationUtility (σ : JointDistribution M N) (G : Game M N)
    (j' : Fin N) : ℝ :=
  ∑ i : Fin M, σ.rowMarginal i * G.colUtility i j'
