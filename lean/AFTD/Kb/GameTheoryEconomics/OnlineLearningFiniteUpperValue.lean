import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PureVsPayoff

/-!
# OnlineLearning.finiteUpperValue

Topic: equilibria   Node: 306af32ec25e

Provenance: formalization of a published result. Source: TCSlib, `OnlineLearning.finiteUpperValue`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{upper value} of $G$ is
\[
  v^+(G) \;=\; \inf_{q \in \Delta_N}\; \sup_{i \in [M]}\; \mathrm{pureVsPayoff}(G,i,q),
\]
where the column player minimises over mixed strategies and the row player
maximises over pure responses.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The upper value of a finite zero-sum game: the infimum over column mixed strategies `q` of the supremum over pure rows `i` of the payoff of `i` against `q` (column commits to a mixed strategy, then row chooses the best pure response). [CBL06, §7.2]. -/
noncomputable def OnlineLearning.finiteUpperValue {M N : ℕ} (G : ZeroSumGame M N) : ℝ :=
  ⨅ q : MixedStrategy N, ⨆ i : Fin M, pureVsPayoff G i q
