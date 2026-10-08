import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PrefixGameLoss
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame

/-!
# prefixHedgeWeight

Topic: equilibria   Node: 678d0b1e2ec3

Provenance: formalization of a published result. Source: TCSlib, `prefixHedgeWeight`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The unnormalised Hedge weight of row $i$ after seeing a prefix of column
actions at learning rate $\eta$ is
\[
  w_t(i) \;=\; \exp\!\bigl(-\eta \cdot L_t(i)\bigr),
\]
where $L_t(i)$ is the prefix cumulative loss.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The Hedge weight `exp(−η · prefixGameLoss)` of row `i`, computed directly from a prefix of column actions. -/
noncomputable def prefixHedgeWeight {M N : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) (i : Fin M) : ℝ :=
  Real.exp (-η * prefixGameLoss G actions i)
