import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxIntactObstructionValues
import AFTD.Kb.GameTheoryEconomics.EfxIntactObstructionCoarse
import AFTD.Kb.GameTheoryEconomics.EfxIntactObstructionNoCoarse
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods

/-!
# efx_intact_obstruction_requires_split

Topic: fair_division   Node: 952357514194

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Explicit route obstruction found in experiment 10980; it does not refute EFX existence and carries no research-level advance claim.

Every EFX allocation of the explicit seven-good positive instance separates goods 0 and 1 or separates goods 2 and 3; hence it splits an old bundle of the stated six-good EFX allocation.
-/

open Function Finset

theorem efx_intact_obstruction_requires_split (σ : Fin 7 → Fin 4) (h01 : σ 0 = σ 1) (h23 : σ 2 = σ 3) :
    ¬ is_efx_goods (fun i g => (efx_intact_obstruction_values i g : ℝ)) σ := by
  let p : Fin 5 → Fin 4 := ![σ 5, σ 0, σ 2, σ 4, σ 6]
  have heq : σ = efx_intact_obstruction_coarse p := by
    funext g
    fin_cases g <;> simp [efx_intact_obstruction_coarse, p, h01, h23]
  rw [heq]
  exact efx_intact_obstruction_no_coarse p
