import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleValues
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.EfxMinCycleBaseline
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_min_cycle_full_efx

Topic: fair_division   Node: 7f0f9f33aabd

Provenance: helper lemma. Explicit two-split completion for the OP-7 minimum-cardinality two-cycle obstruction; experiments 11452 and 11453.

The instance has a complete EFX allocation with owners (0,0,0,0,1,3,2,2,2,3,2,1,1) that strictly improves all four original utilities; it preserves old triples 0 and 2 and splits old triples 1 and 3.
-/

theorem efx_min_cycle_full_efx :
  is_efx_goods (fun i g => (efx_min_cycle_values i g : ℝ))
    ![(0 : Fin 4),0,0,0,1,3,2,2,2,3,2,1,1] ∧
  ∀ i : Fin 4, (efx_min_cycle_baseline i : ℝ) <
    additive_valuation (fun g => (efx_min_cycle_values i g : ℝ))
      (bundle_of ![(0 : Fin 4),0,0,0,1,3,2,2,2,3,2,1,1] i) := by
  constructor
  · rw [is_efx_goods_nat_cast_iff]
    decide
  · have hh : ∀ i : Fin 4, efx_min_cycle_baseline i <
      ∑ g ∈ bundle_of ![(0 : Fin 4),0,0,0,1,3,2,2,2,3,2,1,1] i, efx_min_cycle_values i g := by
      decide
    intro i
    simp only [additive_valuation]
    exact_mod_cast hh i
