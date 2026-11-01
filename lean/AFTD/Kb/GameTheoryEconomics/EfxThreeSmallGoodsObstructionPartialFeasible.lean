import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionOriginalThreshold
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionPartialValues
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionPartialCoarse
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionPartialOwn

/-!
# efx_three_small_goods_obstruction_partial_feasible

Topic: fair_division   Node: 0926745793f5

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

A two-bonus coarse allocation is feasible when it weakly preserves every original old-only utility and satisfies all exact natural-number EFX inequalities for that ten-good restriction.
-/

open Function Finset

def efx_three_small_goods_obstruction_partial_feasible (t : Fin 3) (q : Fin 6 → Fin 4) : Prop :=(∀ i, efx_three_small_goods_obstruction_original_threshold i ≤ efx_three_small_goods_obstruction_partial_own t q i) ∧
  (∀ i j : Fin 4, i ≠ j → ∀ g : Fin 10, efx_three_small_goods_obstruction_partial_coarse q g = j →
    (∑ h : Fin 10, if efx_three_small_goods_obstruction_partial_coarse q h = j then efx_three_small_goods_obstruction_partial_values t i h else 0) ≤
      efx_three_small_goods_obstruction_partial_own t q i + efx_three_small_goods_obstruction_partial_values t i g)
