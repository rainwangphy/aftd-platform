import AFTD.Prelude

/-!
# efx_intact_obstruction_values

Topic: fair_division   Node: 5829c989084c

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Explicit route obstruction found in experiment 10980; it does not refute EFX existence and carries no research-level advance claim.

The explicit strictly positive four-agent seven-good valuation matrix used to test completion by keeping old bundles intact: rows (1,2,2,1,4,5,4), (2,1,2,2,5,5,2), (4,1,2,5,5,4,4), and (1,2,2,1,5,3,4).
-/

open Function Finset

def efx_intact_obstruction_values : Fin 4 → Fin 7 → ℕ :=![![1,2,2,1,4,5,4], ![2,1,2,2,5,5,2], ![4,1,2,5,5,4,4], ![1,2,2,1,5,3,4]]
