import AFTD.Prelude

/-!
# efx_pair_binary_values

Topic: fair_division   Node: 4e2c0b57d233

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Exact route obstruction from experiment 10993, not a counterexample to EFX existence; no novelty claim.

A positive four-agent nine-good valuation matrix: the first two rows are (2,1,2,1,2,1,2,1,2), and the last two rows are (1,2,1,2,1,2,1,2,2).
-/

open Function Finset

def efx_pair_binary_values : Fin 4 → Fin 9 → ℕ :=![![2,1,2,1,2,1,2,1,2], ![2,1,2,1,2,1,2,1,2],
    ![1,2,1,2,1,2,1,2,2], ![1,2,1,2,1,2,1,2,2]]
