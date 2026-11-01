import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionPartialValues
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionPartialCoarse

/-!
# efx_three_small_goods_obstruction_partial_own

Topic: fair_division   Node: 41c1e295220a

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

The exact natural-number own utility of agent i in the two-bonus restriction indexed t under the coarse allocation q.
-/

open Function Finset

def efx_three_small_goods_obstruction_partial_own (t : Fin 3) (q : Fin 6 → Fin 4) (i : Fin 4) : ℕ :=∑ g : Fin 10, if efx_three_small_goods_obstruction_partial_coarse q g = i then efx_three_small_goods_obstruction_partial_values t i g else 0
