import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxNondegCycleValues
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_nondeg_cycle_full_efx

Topic: fair_division   Node: d8d1b3825e3c

Provenance: helper lemma. Nondegenerate three-source champion two-cycle exchange obstruction for OP-7, experiments 11481–11487; related arXiv:2002.05119 Section 3.1.

The nondegenerate instance has a complete EFX allocation with owners (0,0,0,0,1,3,2,2,2,3,2,1,1).
-/

theorem efx_nondeg_cycle_full_efx :
  is_efx_goods (fun i g => (efx_nondeg_cycle_values i g : ℝ))
    ![(0 : Fin 4),0,0,0,1,3,2,2,2,3,2,1,1] := by
  rw [is_efx_goods_nat_cast_iff]
  decide
