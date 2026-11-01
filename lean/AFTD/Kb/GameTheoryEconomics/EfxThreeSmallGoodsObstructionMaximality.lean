import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionThreshold
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionPartialOwn
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionPartialFeasible
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionPartialCoarse
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionValues
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionOriginalThreshold
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionPartialValues

/-!
# efx_three_small_goods_obstruction_maximality

Topic: fair_division   Node: 3fbd873d464d

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

For every choice of omitted bonus t and every coarse allocation q keeping the four old pairs intact, if the two-bonus restriction satisfies EFX and weakly preserves all original old-only utilities, its total own utility is at most 4475. If equality holds, its four own utilities equal the current threshold vector (883,1992,800,800).
-/

open Function Finset

theorem efx_three_small_goods_obstruction_maximality : ∀ (t : Fin 3) (q : Fin 6 → Fin 4),
    efx_three_small_goods_obstruction_partial_feasible t q →
      (∑ i : Fin 4, efx_three_small_goods_obstruction_partial_own t q i) ≤ 4475 ∧
      ((∑ i : Fin 4, efx_three_small_goods_obstruction_partial_own t q i) = 4475 →
        ∀ i, efx_three_small_goods_obstruction_partial_own t q i = efx_three_small_goods_obstruction_threshold i) := by
  unfold efx_three_small_goods_obstruction_partial_feasible efx_three_small_goods_obstruction_partial_own
    efx_three_small_goods_obstruction_partial_coarse efx_three_small_goods_obstruction_partial_values
    efx_three_small_goods_obstruction_threshold efx_three_small_goods_obstruction_original_threshold
    efx_three_small_goods_obstruction_values
  decide +kernel
