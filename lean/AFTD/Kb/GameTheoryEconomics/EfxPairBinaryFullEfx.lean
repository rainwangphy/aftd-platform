import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.EfxPairBinaryValues
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_pair_binary_full_efx

Topic: fair_division   Node: e5eaeb6f0592

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Exact route obstruction from experiment 10993, not a counterexample to EFX existence; no novelty claim.

For the explicit binary nine-good valuation matrix cast to real values, the full allocation (3,3,1,2,0,2,1,1,0), listing the owner of each good, is EFX.
-/

open Function Finset

theorem efx_pair_binary_full_efx :
    is_efx_goods (fun i g => (efx_pair_binary_values i g : ℝ))
      ![(3 : Fin 4),3,1,2,0,2,1,1,0] := by
  rw [is_efx_goods_nat_cast_iff]
  decide
