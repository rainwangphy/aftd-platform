import AFTD.Prelude

/-!
# efx_intact_obstruction_coarse

Topic: fair_division   Node: b915c4523c64

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Explicit route obstruction found in experiment 10980; it does not refute EFX existence and carries no research-level advance claim.

Assign the four old bundles {5}, {0,1}, {2,3}, {4} and the new singleton {6} to arbitrary agents p(0),...,p(4), respectively; mergers and empty recipients are permitted.
-/

open Function Finset

def efx_intact_obstruction_coarse (p : Fin 5 → Fin 4) : Fin 7 → Fin 4 :=![p 1,p 1,p 2,p 2,p 3,p 0,p 4]
