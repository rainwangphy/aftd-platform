import AFTD.Prelude

/-!
# efx_pair_binary_one_split

Topic: fair_division   Node: 112a69c6707b

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Exact route obstruction from experiment 10993, not a counterexample to EFX existence; no novelty claim.

Assign the four old adjacent pairs among goods 0 through 7 and the new good 8 to arbitrary agents, except the pair indexed r may have its two goods assigned separately. Six arbitrary agent parameters encode the split pair, the three intact pairs, and the new good; mergers are allowed.
-/

open Function Finset

def efx_pair_binary_one_split (r : Fin 4) (a b c d e f : Fin 4) : Fin 9 → Fin 4 :=(![![a,b,c,c,d,d,e,e,f], ![a,a,b,c,d,d,e,e,f],
    ![a,a,b,b,c,d,e,e,f], ![a,a,b,b,c,c,d,e,f]] : Fin 4 → Fin 9 → Fin 4) r
