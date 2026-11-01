import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAllsourceThreePairPerturbedValues
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_allsource_three_pair_perturbed_strict_sanity

Topic: fair_division   Node: 1acf298d0d82

Provenance: helper lemma. Binary perturbation of the four-agent three-split barrier; experiment 11706 and the integer-gap projection.

The perturbed partial state is strictly envy-free, and the explicit complete allocation remains EFX.
-/

theorem efx_allsource_three_pair_perturbed_strict_sanity :
  (∀ i g, 0 < efx_allsource_three_pair_perturbed_values i g) ∧
  (∀ (i j : Fin 4), i ≠ j →
    efx_allsource_three_pair_perturbed_values i (![0,2,4,6] j) + efx_allsource_three_pair_perturbed_values i (![1,3,5,7] j) <
      efx_allsource_three_pair_perturbed_values i (![0,2,4,6] i) + efx_allsource_three_pair_perturbed_values i (![1,3,5,7] i)) ∧
  is_efx_goods (fun i g => (efx_allsource_three_pair_perturbed_values i g : ℝ)) ![(0 : Fin 4),0,1,3,2,0,1,2,3] := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  apply (is_efx_goods_nat_cast_iff _ _).mpr
  decide +kernel
