import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PrefixHedgeWeight
import AFTD.Kb.GameTheoryEconomics.PrefixHedgeWeightPos
import AFTD.Kb.GameTheoryEconomics.PrefixPotential
import AFTD.Kb.GameTheoryEconomics.PrefixPotentialPos
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame

/-!
# prefixHedgeMixedStrategy

Topic: equilibria   Node: 8eb24f1f16d5

Provenance: formalization of a published result. Source: TCSlib, `prefixHedgeMixedStrategy`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The normalised Hedge distribution after a prefix of $t$ column actions is the
mixed row strategy with weights
\[
  p_t(i) \;=\; \frac{w_t(i)}{\Phi_t},
\]
where $w_t(i)$ is the prefix Hedge weight and $\Phi_t$ the prefix potential.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The row player's Hedge mixed strategy after seeing a prefix of column actions: row `i` gets weight `prefixHedgeWeight i / prefixPotential`. -/
noncomputable def prefixHedgeMixedStrategy {M N : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) : MixedStrategy M where
  weights i := prefixHedgeWeight G η actions i / prefixPotential G η actions
  nonneg i := div_nonneg (prefixHedgeWeight_pos G η actions i).le
    (prefixPotential_pos G η actions).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (prefixPotential_pos G η actions))
