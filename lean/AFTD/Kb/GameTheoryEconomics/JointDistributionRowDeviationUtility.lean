import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Game
import AFTD.Kb.GameTheoryEconomics.JointDistribution
import AFTD.Kb.GameTheoryEconomics.JointDistributionColMarginal

/-!
# JointDistribution.rowDeviationUtility

Topic: equilibria   Node: d575d28660ea

Provenance: formalization of a published result. Source: TCSlib, `JointDistribution.rowDeviationUtility`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The row player's expected utility from unilaterally deviating to the fixed
pure action $i'$, while the column player keeps $\sigma$'s column marginal:
$\sum_{j} \sigma^{\mathrm{col}}_j \cdot u_r(i', j)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
variable {M N : ℕ} in
/-- The row player's expected utility from unilaterally deviating to the pure action `i'` while the column player's action is still drawn from `σ`'s column marginal. [Rou13-L13, §3]. -/
noncomputable def JointDistribution.rowDeviationUtility (σ : JointDistribution M N) (G : Game M N)
    (i' : Fin M) : ℝ :=
  ∑ j : Fin N, σ.colMarginal j * G.rowUtility i' j
