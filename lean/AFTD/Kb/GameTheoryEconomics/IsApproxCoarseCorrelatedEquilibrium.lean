import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Game
import AFTD.Kb.GameTheoryEconomics.JointDistribution
import AFTD.Kb.GameTheoryEconomics.JointDistributionColDeviationUtility
import AFTD.Kb.GameTheoryEconomics.JointDistributionColExpectedUtility
import AFTD.Kb.GameTheoryEconomics.JointDistributionRowDeviationUtility
import AFTD.Kb.GameTheoryEconomics.JointDistributionRowExpectedUtility

/-!
# IsApproxCoarseCorrelatedEquilibrium

Topic: equilibria   Node: b2a87e169724

Provenance: formalization of a published result. Source: TCSlib, `IsApproxCoarseCorrelatedEquilibrium`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A joint distribution $\sigma$ is an \emph{$\varepsilon$-coarse correlated
equilibrium} ($\varepsilon$-CCE) of game $G$ if each player's gain from any
unilateral pure deviation is at most $\varepsilon$: for all $i'$,
$\mathrm{rowDevUtil}(\sigma, G, i') \le \mathrm{rowExpUtil}(\sigma, G) + \varepsilon$,
and similarly for the column player.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- A joint distribution `σ` is an **ε-coarse correlated equilibrium** of `G` if each unilateral commitment to a fixed pure action improves a player's expected utility by at most `ε`. [Rou13-L13, §3]; [Rou13-L17, Prop. 3.1]; [CBL06, §7.4]. Deviation: two players only, with utilities written as explicit sums over `Fin M × Fin N`. -/
def IsApproxCoarseCorrelatedEquilibrium {M N : ℕ} (G : Game M N)
    (σ : JointDistribution M N) (ε : ℝ) : Prop :=
  (∀ i' : Fin M, σ.rowDeviationUtility G i' ≤ σ.rowExpectedUtility G + ε) ∧
  (∀ j' : Fin N, σ.colDeviationUtility G j' ≤ σ.colExpectedUtility G + ε)
