import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAnchorLockPerturbedValues
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_anchor_lock_full_efx

Topic: fair_division   Node: 5f08ff9e1f11

Provenance: helper lemma. Nondegenerate no-singleton four-agent Pareto-maximal partial EFX obstruction, experiments 11500–11507; locked-good lift of arXiv:2002.05119 Section 5.

The nondegenerate instance has a complete EFX allocation with owners (3,1,1,1,2,2,1,2,1,0,3,0).
-/

theorem efx_anchor_lock_full_efx :
  is_efx_goods (fun i g => (efx_anchor_lock_perturbed_values i g : ℝ))
    ![(3 : Fin 4),1,1,1,2,2,1,2,1,0,3,0] := by
  rw [is_efx_goods_nat_cast_iff]
  decide
