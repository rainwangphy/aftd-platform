import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Game
import AFTD.Kb.GameTheoryEconomics.JointDistribution

/-!
# JointDistribution.colExpectedUtility

Topic: equilibria   Node: 567786224515

Provenance: formalization of a published result. Source: TCSlib, `JointDistribution.colExpectedUtility`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The column player's expected utility under $\sigma$ in game $G$ is
$\sum_{i,j} \sigma_{ij} \cdot u_c(i,j)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
variable {M N : ℕ} in
/-- The column player's expected utility under the joint distribution `σ`: the `σ`-weighted sum of the column utilities over all action profiles. [Rou13-L13, Def. 3.4]. -/
noncomputable def JointDistribution.colExpectedUtility (σ : JointDistribution M N) (G : Game M N) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin N, σ.prob i j * G.colUtility i j
