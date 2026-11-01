import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxIntactObstructionValues
import AFTD.Kb.GameTheoryEconomics.EfxIntactObstructionCoarse

/-!
# efx_intact_obstruction_no_coarse_nat

Topic: fair_division   Node: c022d3d29ef8

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Explicit route obstruction found in experiment 10980; it does not refute EFX existence and carries no research-level advance claim.

Every assignment of the four intact old bundles and the new singleton in the explicit seven-good instance violates an EFX inequality, checked with exact natural-number sums.
-/

open Function Finset

theorem efx_intact_obstruction_no_coarse_nat : ∀ p : Fin 5 → Fin 4, ¬ (∀ i j : Fin 4, i ≠ j → ∀ g : Fin 7,
    efx_intact_obstruction_coarse p g = j →
    (∑ h : Fin 7, if efx_intact_obstruction_coarse p h = j then efx_intact_obstruction_values i h else 0) ≤
    (∑ h : Fin 7, if efx_intact_obstruction_coarse p h = i then efx_intact_obstruction_values i h else 0) + efx_intact_obstruction_values i g) := by
  decide +kernel
