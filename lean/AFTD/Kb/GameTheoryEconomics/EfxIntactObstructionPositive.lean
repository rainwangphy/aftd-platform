import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxIntactObstructionValues

/-!
# efx_intact_obstruction_positive

Topic: fair_division   Node: c7edc6588896

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Explicit route obstruction found in experiment 10980; it does not refute EFX existence and carries no research-level advance claim.

Every entry of the explicit four-agent seven-good valuation matrix is strictly positive after casting to the reals.
-/

open Function Finset

theorem efx_intact_obstruction_positive : ∀ (i : Fin 4) (g : Fin 7), 0 < (efx_intact_obstruction_values i g : ℝ) := by
  intro i g
  exact_mod_cast (show 0 < efx_intact_obstruction_values i g from (by decide +kernel :
    ∀ (j : Fin 4) (h : Fin 7), 0 < efx_intact_obstruction_values j h) i g)
