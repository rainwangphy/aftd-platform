import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.EfxIntactObstructionValues
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_intact_obstruction_partial_efx

Topic: fair_division   Node: dc184f6062ae

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Explicit route obstruction found in experiment 10980; it does not refute EFX existence and carries no research-level advance claim.

In the explicit seven-good instance restricted to the first six goods, assigning {5} to agent 0, {0,1} to agent 1, {2,3} to agent 2, and {4} to agent 3 is EFX.
-/

open Function Finset

theorem efx_intact_obstruction_partial_efx :
    is_efx_goods (fun i (g : Fin 6) => (efx_intact_obstruction_values i g.castSucc : ℝ))
      ![(1 : Fin 4),1,2,2,3,0] := by
  apply (is_efx_goods_nat_cast_iff _ _).mpr
  decide +kernel
