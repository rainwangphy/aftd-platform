import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame

/-!
# prefixGameLoss

Topic: equilibria   Node: 3b2cf5755315

Provenance: formalization of a published result. Source: TCSlib, `prefixGameLoss`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a game $G$, a prefix of $t$ column actions, and a row $i$, the
\emph{prefix cumulative loss} of row $i$ is
\[
  L_t(i) \;=\; \sum_{s=0}^{t-1} \bigl(1 - A_{i, a_s}\bigr).
\]
This mirrors \texttt{cumLoss} from the abstract Hedge framework, expressed
directly in terms of game payoffs.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The cumulative game loss `Σ_{s < t} (1 − A(i, j_s))` of row `i` along a finite prefix `j_0, …, j_{t−1}` of column actions. -/
noncomputable def prefixGameLoss {M N : ℕ} (G : ZeroSumGame M N)
    {t : ℕ} (actions : Fin t → Fin N) (i : Fin M) : ℝ :=
  ∑ s : Fin t, (1 - G.payoff i (actions s))
