import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionFeasibleNat
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionNoZeroNat
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionNoOneNat
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionNoTwoNat
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionNoThreeNat

/-!
# efx_three_small_goods_obstruction_no_nat

Topic: fair_division   Node: c1196d829e5e

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

No coarse allocation of the explicit eleven-good instance both weakly preserves the current utility thresholds and satisfies every natural-number EFX inequality.
-/

open Function Finset

theorem efx_three_small_goods_obstruction_no_nat (p : Fin 7 → Fin 4) :
    ¬ efx_three_small_goods_obstruction_feasible_nat p := by
  have hp : p = ![p 0,p 1,p 2,p 3,p 4,p 5,p 6] := by
    funext i
    fin_cases i <;> rfl
  rw [hp]
  generalize p 0 = a, p 1 = b, p 2 = c, p 3 = d, p 4 = e, p 5 = f, p 6 = g
  fin_cases a
  · exact efx_three_small_goods_obstruction_no_zero_nat b c d e f g
  · exact efx_three_small_goods_obstruction_no_one_nat b c d e f g
  · exact efx_three_small_goods_obstruction_no_two_nat b c d e f g
  · exact efx_three_small_goods_obstruction_no_three_nat b c d e f g
