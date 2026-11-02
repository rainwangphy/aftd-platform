import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxSourceTwoValues
import AFTD.Kb.GameTheoryEconomics.EfxSourceTwoStart
import AFTD.Kb.GameTheoryEconomics.EfxSourceTwoWitness
import AFTD.Kb.GameTheoryEconomics.EfxPartialNatUtility
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_source_two_full_efx

Topic: fair_division   Node: d57a83548d0e

Provenance: helper lemma. Nine-good isolated-source completion obstruction derived from the three-agent partial Pareto barrier in arXiv:2002.05119, Section 5; experiments 11561–11562.

The explicit complete EFX allocation preserves the other three initial utilities.
-/

theorem efx_source_two_full_efx :
  is_efx_goods (fun i g => (efx_source_two_values i g : ℝ)) efx_source_two_witness ∧
  (∀ i : Fin 3, (efx_partial_nat_utility efx_source_two_values efx_source_two_start i.castSucc : ℝ) ≤
    additive_valuation (fun g => (efx_source_two_values i.castSucc g : ℝ))
      (bundle_of efx_source_two_witness i.castSucc)) := by
  constructor
  · rw [is_efx_goods_nat_cast_iff]
    decide
  · have hh : ∀ i : Fin 3,
      efx_partial_nat_utility efx_source_two_values efx_source_two_start i.castSucc ≤
      ∑ g ∈ bundle_of efx_source_two_witness i.castSucc, efx_source_two_values i.castSucc g := by
      decide
    intro i
    simp only [additive_valuation]
    exact_mod_cast hh i
