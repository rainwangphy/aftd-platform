import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAllsourceThreePairValues
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_allsource_three_pair_sanity

Topic: fair_division   Node: d6d22f88de06

Provenance: helper lemma. Four-agent envy-free one-charity three-split barrier for OP-7; SMT experiment 11699 and independent enumeration 11701. Both are evidence, not Lean proofs.

The partial allocation is envy-free; all values are positive and charity is owner-small; the explicit full EFX allocation preserves all starting utilities.
-/

theorem efx_allsource_three_pair_sanity :
  (∀ i g, 0 < efx_allsource_three_pair_values i g) ∧
  (∀ (i j : Fin 4), efx_allsource_three_pair_values i (![0,2,4,6] j) + efx_allsource_three_pair_values i (![1,3,5,7] j) ≤ 10) ∧
  (∀ (i : Fin 4), efx_allsource_three_pair_values i (![0,2,4,6] i) + efx_allsource_three_pair_values i (![1,3,5,7] i) = 10) ∧
  (∀ (i : Fin 4), efx_allsource_three_pair_values i 8 ≤ efx_allsource_three_pair_values i (![0,2,4,6] i) ∧
    efx_allsource_three_pair_values i 8 ≤ efx_allsource_three_pair_values i (![1,3,5,7] i)) ∧
  is_efx_goods (fun i (g : Fin 8) => (efx_allsource_three_pair_values i g.castSucc : ℝ)) ![(0 : Fin 4),0,1,1,2,2,3,3] ∧
  is_efx_goods (fun i g => (efx_allsource_three_pair_values i g : ℝ)) ![(0 : Fin 4),0,1,3,2,0,1,2,3] ∧
  (∀ i : Fin 4, (10 : ℝ) ≤ additive_valuation
    (fun g => (efx_allsource_three_pair_values i g : ℝ)) (bundle_of ![(0 : Fin 4),0,1,3,2,0,1,2,3] i)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · apply (is_efx_goods_nat_cast_iff _ _).mpr
    decide +kernel
  · apply (is_efx_goods_nat_cast_iff _ _).mpr
    decide +kernel
  · intro i
    dsimp [additive_valuation]
    fin_cases i <;> norm_cast
