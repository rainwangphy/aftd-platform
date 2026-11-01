import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionValues
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionCoarse
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionThreshold

/-!
# efx_three_small_goods_obstruction_feasible_nat

Topic: fair_division   Node: c5999d171205

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

The exact natural-number condition that a coarse eleven-good allocation both weakly preserves all four current utility thresholds and satisfies every total-value EFX inequality.
-/

open Function Finset

def efx_three_small_goods_obstruction_feasible_nat (p : Fin 7 → Fin 4) : Prop :=(∀ i : Fin 4, efx_three_small_goods_obstruction_threshold i ≤
    ∑ h : Fin 11, if efx_three_small_goods_obstruction_coarse p h = i then efx_three_small_goods_obstruction_values i h else 0) ∧
  (∀ i j : Fin 4, i ≠ j → ∀ g : Fin 11, efx_three_small_goods_obstruction_coarse p g = j →
    (∑ h : Fin 11, if efx_three_small_goods_obstruction_coarse p h = j then efx_three_small_goods_obstruction_values i h else 0) ≤
    (∑ h : Fin 11, if efx_three_small_goods_obstruction_coarse p h = i then efx_three_small_goods_obstruction_values i h else 0) +
      efx_three_small_goods_obstruction_values i g)
