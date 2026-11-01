import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNoSelfThreeSplitValues
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_no_self_three_split_full_efx

Topic: fair_division   Node: 4b791860111b

Provenance: helper lemma. Positive equal-triple no-self-champion obstruction to the OP-7 two-bundle exchange route, experiments 11462–11471.

A complete EFX allocation of the matrix has owners (2,1,2,1,3,2,3,1,0,0,0,0,0).
-/

theorem efx_no_self_three_split_full_efx :
  is_efx_goods (fun i g => (efx_no_self_three_split_values i g : ℝ))
    ![(2 : Fin 4),1,2,1,3,2,3,1,0,0,0,0,0] := by
  rw [is_efx_goods_nat_cast_iff]
  decide
