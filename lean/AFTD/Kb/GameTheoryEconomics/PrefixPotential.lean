import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PrefixHedgeWeight

/-!
# prefixPotential

Topic: equilibria   Node: 18d0593e5be4

Provenance: formalization of a published result. Source: TCSlib, `prefixPotential`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{prefix potential} is the sum of prefix Hedge weights over all rows:
\[
  \Phi_t \;=\; \sum_{i \in \mathrm{Fin}\,M} w_t(i).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The prefix potential: the sum over rows of the prefix Hedge weights. -/
noncomputable def prefixPotential {M N : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) : ℝ :=
  ∑ i : Fin M, prefixHedgeWeight G η actions i
