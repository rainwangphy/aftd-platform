import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionValues
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionCoarse
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionThreshold
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionNoNat
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.AdditiveValuationBundleSumIte
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_three_small_goods_obstruction_no_current_ir

Topic: fair_division   Node: ffecb5144ad3

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

In the explicit eleven-good instance cast to real values, every EFX coarse completion has some agent whose utility is strictly less than her current utility threshold.
-/

open Function Finset

theorem efx_three_small_goods_obstruction_no_current_ir (p : Fin 7 → Fin 4)
    (hEF : is_efx_goods (fun i g => (efx_three_small_goods_obstruction_values i g : ℝ)) (efx_three_small_goods_obstruction_coarse p)) :
    ∃ i : Fin 4, additive_valuation (fun g => (efx_three_small_goods_obstruction_values i g : ℝ))
      (bundle_of (efx_three_small_goods_obstruction_coarse p) i) < (efx_three_small_goods_obstruction_threshold i : ℝ) := by
  classical
  by_contra h
  push Not at h
  apply efx_three_small_goods_obstruction_no_nat p
  constructor
  · intro i
    have hi := h i
    rw [additive_valuation_bundle_sum_ite] at hi
    have hcast :
        (∑ g, if efx_three_small_goods_obstruction_coarse p g = i then
            (efx_three_small_goods_obstruction_values i g : ℝ) else 0)
          = ((∑ g, if efx_three_small_goods_obstruction_coarse p g = i then
              efx_three_small_goods_obstruction_values i g else 0 : ℕ) : ℝ) := by
      push_cast
      rfl
    rw [hcast] at hi
    exact_mod_cast hi
  · intro i j hij g hg
    have hh := (is_efx_goods_nat_cast_iff efx_three_small_goods_obstruction_values
      (efx_three_small_goods_obstruction_coarse p)).mp hEF
    have hm : g ∈ bundle_of (efx_three_small_goods_obstruction_coarse p) j := by
      simpa [bundle_of] using hg
    have := hh i j hij g hm
    simpa only [bundle_of, Finset.sum_filter] using this
