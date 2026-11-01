import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitPerturbedValues
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_no_self_three_split_perturbed_full

Topic: fair_division   Node: cf24ef6ffddc

Provenance: helper lemma. Nondegenerate strengthening of the OP-7 no-self three-split obstruction, experiments 11492–11494; related perturbation argument arXiv:2002.05119 Lemma 1.

The nondegenerate perturbation admits a complete EFX allocation with owners (2,1,2,1,3,2,3,1,0,0,0,0,0).
-/

theorem efx_no_self_three_split_perturbed_full :
  is_efx_goods (fun i g => (efx_no_self_three_split_perturbed_values i g : ℝ))
    ![(2 : Fin 4),1,2,1,3,2,3,1,0,0,0,0,0] := by
  rw [is_efx_goods_nat_cast_iff]
  decide
