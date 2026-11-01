import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctValues
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_three_bonus_distinct_sanity

Topic: fair_division   Node: 2b8813a61215

Provenance: helper lemma. Finite obstruction to the distinct-recipient exchange route for OP-7, experiments 11403, 11405 and 11406.

Every value in the explicit matrix is positive and each bonus is no larger than every old good for each agent. The old allocation (0,1,2,3) is EFX with utility 38 for each agent. The complete allocation (0,1,2,3,0,0,0) is EFX and gives each agent at least 38.
-/

theorem efx_three_bonus_distinct_sanity :
    (∀ i g, 0 < efx_three_bonus_distinct_values i g) ∧
    (∀ (i : Fin 4) (g : Fin 3) (h : Fin 4),
      efx_three_bonus_distinct_values i (Fin.natAdd 4 g) ≤ efx_three_bonus_distinct_values i (Fin.castAdd 3 h)) ∧
    is_efx_goods (fun i (g : Fin 4) => (efx_three_bonus_distinct_values i (Fin.castAdd 3 g) : ℝ)) ![(0 : Fin 4),1,2,3] ∧
    is_efx_goods (fun i g => (efx_three_bonus_distinct_values i g : ℝ)) ![(0 : Fin 4),1,2,3,0,0,0] ∧
    (∀ i : Fin 4, additive_valuation (fun g : Fin 4 => (efx_three_bonus_distinct_values i (Fin.castAdd 3 g) : ℝ))
      (bundle_of ![(0 : Fin 4),1,2,3] i) = 38) ∧
    (∀ i : Fin 4, 38 ≤ additive_valuation (fun g => (efx_three_bonus_distinct_values i g : ℝ))
      (bundle_of ![(0 : Fin 4),1,2,3,0,0,0] i)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_, ?_, ?_⟩
  · apply (is_efx_goods_nat_cast_iff _ _).mpr
    decide +kernel
  · apply (is_efx_goods_nat_cast_iff _ _).mpr
    decide +kernel
  · intro i
    dsimp [additive_valuation]
    fin_cases i <;> norm_cast
  · intro i
    dsimp [additive_valuation]
    fin_cases i <;> norm_cast
