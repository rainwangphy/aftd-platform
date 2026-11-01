import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionValues

/-!
# efx_three_small_goods_obstruction_partial_values

Topic: fair_division   Node: 993ccba2232a

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

The ten-good restriction of the explicit eleven-good matrix obtained by retaining all eight old goods and omitting bonus good 8+t, with the two retained bonuses listed in increasing index order.
-/

open Function Finset

def efx_three_small_goods_obstruction_partial_values (t : Fin 3) (i : Fin 4) (g : Fin 10) : ℕ :=efx_three_small_goods_obstruction_values i ((![![0,1,2,3,4,5,6,7,9,10],
    ![0,1,2,3,4,5,6,7,8,10], ![0,1,2,3,4,5,6,7,8,9]] : Fin 3 → Fin 10 → Fin 11) t g)
