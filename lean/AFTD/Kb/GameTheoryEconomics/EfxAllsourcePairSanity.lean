import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAllsourcePairValues
import AFTD.Kb.GameTheoryEconomics.EfxAllsourcePairBaseline
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_allsource_pair_sanity

Topic: fair_division   Node: 1daf24180402

Provenance: helper lemma. Three-valued all-source no-self two-split EFX obstruction for OP-7; experiments 11638–11642.

The old state is envy-free with all values positive and charity small for each owner; the explicit complete witness is EFX and IR.
-/

theorem efx_allsource_pair_sanity :
  (∀ i g, 0 < efx_allsource_pair_values i g) ∧
  (∀ (i j : Fin 4),
    efx_allsource_pair_values i (![0,2,4,6] j) + efx_allsource_pair_values i (![1,3,5,7] j) = efx_allsource_pair_baseline i) ∧
  (∀ (i : Fin 4), efx_allsource_pair_values i 8 ≤ efx_allsource_pair_values i (![0,2,4,6] i) ∧
    efx_allsource_pair_values i 8 ≤ efx_allsource_pair_values i (![1,3,5,7] i)) ∧
  is_efx_goods (fun i (g : Fin 8) => (efx_allsource_pair_values i g.castSucc : ℝ)) ![(0 : Fin 4),0,1,1,2,2,3,3] ∧
  is_efx_goods (fun i g => (efx_allsource_pair_values i g : ℝ)) ![(0 : Fin 4),0,1,0,1,2,3,3,2] ∧
  (∀ i : Fin 4, (efx_allsource_pair_baseline i : ℝ) ≤ additive_valuation
    (fun g => (efx_allsource_pair_values i g : ℝ)) (bundle_of ![(0 : Fin 4),0,1,0,1,2,3,3,2] i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · refine (is_efx_goods_nat_cast_iff
      (v := fun i (g : Fin 8) => efx_allsource_pair_values i g.castSucc) _).mpr ?_
    decide
  · refine (is_efx_goods_nat_cast_iff
      (v := fun i (g : Fin 9) => efx_allsource_pair_values i g) _).mpr ?_
    decide
  · have hnat : ∀ i : Fin 4, efx_allsource_pair_baseline i ≤
        ∑ g ∈ bundle_of ![(0 : Fin 4),0,1,0,1,2,3,3,2] i, efx_allsource_pair_values i g := by
      decide
    intro i
    have hcast : ((efx_allsource_pair_baseline i : ℕ) : ℝ) ≤
        ((∑ g ∈ bundle_of ![(0 : Fin 4),0,1,0,1,2,3,3,2] i,
          efx_allsource_pair_values i g : ℕ) : ℝ) := by
      exact_mod_cast hnat i
    have hsum : additive_valuation (fun g => (efx_allsource_pair_values i g : ℝ))
        (bundle_of ![(0 : Fin 4),0,1,0,1,2,3,3,2] i)
        = ((∑ g ∈ bundle_of ![(0 : Fin 4),0,1,0,1,2,3,3,2] i,
            efx_allsource_pair_values i g : ℕ) : ℝ) := by
      simp [additive_valuation, Nat.cast_sum]
    rw [hsum]
    exact hcast
