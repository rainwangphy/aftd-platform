import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.EfxIntactObstructionValues
import AFTD.Kb.GameTheoryEconomics.EfxIntactObstructionCoarse
import AFTD.Kb.GameTheoryEconomics.EfxIntactObstructionNoCoarseNat
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# efx_intact_obstruction_no_coarse

Topic: fair_division   Node: 0e2ad0b9f565

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Explicit route obstruction found in experiment 10980; it does not refute EFX existence and carries no research-level advance claim.

No assignment of the four intact old bundles and new singleton in the explicit seven-good instance is EFX after casting its item values to reals.
-/

open Function Finset

theorem efx_intact_obstruction_no_coarse (p : Fin 5 → Fin 4) :
    ¬ is_efx_goods (fun i g => (efx_intact_obstruction_values i g : ℝ)) (efx_intact_obstruction_coarse p) := by
  intro h
  have hh := (is_efx_goods_nat_cast_iff efx_intact_obstruction_values (efx_intact_obstruction_coarse p)).mp h
  apply efx_intact_obstruction_no_coarse_nat p
  intro i j hij g hg
  have hg' : g ∈ bundle_of (efx_intact_obstruction_coarse p) j := by simpa [bundle_of] using hg
  have h' := hh i j hij g hg'
  simpa only [bundle_of, Finset.sum_filter] using h'
