import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionFeasibleNat
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionCoarse
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionValues
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionThreshold

/-!
# efx_three_small_goods_obstruction_no_three_nat

Topic: fair_division   Node: 7afa5af4f0a1

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

Every coarse allocation whose first old pair is given to agent 3 fails the conjunction of current utility preservation and the exact natural-number EFX inequalities in the explicit eleven-good instance.
-/

open Function Finset

theorem efx_three_small_goods_obstruction_no_three_nat : ∀ b c d e f g : Fin 4,
    ¬ efx_three_small_goods_obstruction_feasible_nat ![3,b,c,d,e,f,g] := by
  unfold efx_three_small_goods_obstruction_feasible_nat
    efx_three_small_goods_obstruction_coarse
    efx_three_small_goods_obstruction_threshold
    efx_three_small_goods_obstruction_values
  decide +kernel
