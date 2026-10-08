import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure

/-!
# OnlineLearning.finiteLowerValue

Topic: equilibria   Node: 27ec8f467b15

Provenance: formalization of a published result. Source: TCSlib, `OnlineLearning.finiteLowerValue`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a finite zero-sum game $G$ with $M$ row actions and $N$ column actions,
the \emph{lower value} is
\[
  v^- (G) \;=\; \sup_{p \in \Delta_M}\; \inf_{j \in [N]}\; \mathrm{payoffVsPure}(G,p,j),
\]
where the row player maximises over mixed strategies and the column player
minimises over pure responses.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The lower value of a finite zero-sum game: the supremum over row mixed strategies `p` of the infimum over pure columns `j` of the payoff of `p` against `j` (row commits to a mixed strategy, then column chooses the worst pure response). [CBL06, §7.2]. -/
noncomputable def OnlineLearning.finiteLowerValue {M N : ℕ} (G : ZeroSumGame M N) : ℝ :=
  ⨆ p : MixedStrategy M, ⨅ j : Fin N, payoffVsPure G p j
