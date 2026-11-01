import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxIntactObstructionValues
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_intact_obstruction_charity_strict

Topic: fair_division   Node: ab05ef14deca

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Explicit route obstruction found in experiment 10980; it does not refute EFX existence and carries no research-level advance claim.

Each agent strictly prefers her assigned bundle in the explicit six-good partial allocation to the unallocated seventh good.
-/

open Function Finset

theorem efx_intact_obstruction_charity_strict : ∀ i : Fin 4, (efx_intact_obstruction_values i 6 : ℝ) <
    additive_valuation (fun g : Fin 6 => (efx_intact_obstruction_values i g.castSucc : ℝ))
      (bundle_of ![(1 : Fin 4),1,2,2,3,0] i) := by
  intro i
  dsimp [additive_valuation]
  exact_mod_cast (show efx_intact_obstruction_values i 6 <
    ∑ g ∈ bundle_of ![(1 : Fin 4),1,2,2,3,0] i, efx_intact_obstruction_values i g.castSucc from
    (by decide +kernel : ∀ j : Fin 4, efx_intact_obstruction_values j 6 <
      ∑ g ∈ bundle_of ![(1 : Fin 4),1,2,2,3,0] j, efx_intact_obstruction_values j g.castSucc) i)
