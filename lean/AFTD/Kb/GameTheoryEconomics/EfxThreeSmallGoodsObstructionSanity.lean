import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionValues
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionThreshold
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionOriginalThreshold
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_three_small_goods_obstruction_sanity

Topic: fair_division   Node: d39b8d1e95fb

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

In the explicit eleven-good instance all natural item values are strictly positive, and each of goods 8,9,10 is no more valuable than every old good 0 through 7 for every agent. The starting allocation of the first ten goods is (0,0,1,1,2,2,3,3,0,1); it is EFX after casting to reals and has own utilities (883,1992,800,800). The full allocation (0,0,1,1,2,2,3,3,0,0,1) is EFX after casting to reals and has own utilities (998,1604,800,800). Assigning the first eight goods in adjacent pairs to the four agents in order gives old-only utilities (800,1600,800,800).
-/

open Function Finset

theorem efx_three_small_goods_obstruction_sanity :
    (∀ i g, 0 < efx_three_small_goods_obstruction_values i g) ∧
    (∀ (i : Fin 4) (g : Fin 3) (h : Fin 8),
      efx_three_small_goods_obstruction_values i (Fin.natAdd 8 g) ≤ efx_three_small_goods_obstruction_values i (Fin.castAdd 3 h)) ∧
    is_efx_goods (fun i (g : Fin 10) => (efx_three_small_goods_obstruction_values i g.castSucc : ℝ))
      ![(0 : Fin 4),0,1,1,2,2,3,3,0,1] ∧
    (∀ i, additive_valuation (fun g : Fin 10 => (efx_three_small_goods_obstruction_values i g.castSucc : ℝ))
      (bundle_of ![(0 : Fin 4),0,1,1,2,2,3,3,0,1] i) = (efx_three_small_goods_obstruction_threshold i : ℝ)) ∧
    is_efx_goods (fun i g => (efx_three_small_goods_obstruction_values i g : ℝ))
      ![(0 : Fin 4),0,1,1,2,2,3,3,0,0,1] ∧
    (∀ i, additive_valuation (fun g => (efx_three_small_goods_obstruction_values i g : ℝ))
      (bundle_of ![(0 : Fin 4),0,1,1,2,2,3,3,0,0,1] i) =
        (![998,1604,800,800] i : ℝ)) ∧
    (∀ i, additive_valuation (fun g : Fin 8 => (efx_three_small_goods_obstruction_values i (Fin.castAdd 3 g) : ℝ))
      (bundle_of ![(0 : Fin 4),0,1,1,2,2,3,3] i) =
        (efx_three_small_goods_obstruction_original_threshold i : ℝ)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_, ?_, ?_, ?_⟩
  · apply (is_efx_goods_nat_cast_iff _ _).mpr
    decide +kernel
  · intro i
    dsimp [additive_valuation]
    fin_cases i <;> norm_cast
  · apply (is_efx_goods_nat_cast_iff _ _).mpr
    decide +kernel
  · intro i
    dsimp [additive_valuation]
    fin_cases i <;> norm_cast
  · intro i
    dsimp [additive_valuation]
    fin_cases i <;> norm_cast
