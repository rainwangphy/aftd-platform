import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.EfxPairBinaryValues
import AFTD.Kb.GameTheoryEconomics.EfxPairBinaryOneSplit
import AFTD.Kb.GameTheoryEconomics.EfxPairBinaryNoOneSplitNat
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_pair_binary_no_one_split

Topic: fair_division   Node: e78e7c62ef2c

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Exact route obstruction from experiment 10993, not a counterexample to EFX existence; no novelty claim.

For the explicit binary nine-good matrix cast to real values, no allocation encoded by the one-split construction is EFX.
-/

open Function Finset

theorem efx_pair_binary_no_one_split (r a b c d e f : Fin 4) :
    ¬ is_efx_goods (fun i g => (efx_pair_binary_values i g : ℝ))
      (efx_pair_binary_one_split r a b c d e f) := by
  intro h
  have hh := (is_efx_goods_nat_cast_iff efx_pair_binary_values (efx_pair_binary_one_split r a b c d e f)).mp h
  apply efx_pair_binary_no_one_split_nat r a b c d e f
  intro i j hij g hg
  have hm : g ∈ bundle_of (efx_pair_binary_one_split r a b c d e f) j := by simpa [bundle_of] using hg
  have h' := hh i j hij g hm
  simpa only [bundle_of, Finset.sum_filter] using h'
