import AFTD.Prelude

/-!
# efx_no_self_three_split_code

Topic: fair_division   Node: 28436ae81f98

Provenance: helper lemma. Positive equal-triple no-self-champion obstruction to the OP-7 two-bundle exchange route, experiments 11462–11471.

For each of the six pairs of intact old triples, encode their owners, the six remaining old-good owners, and the charity-good owner; q assigns the nine resulting atoms to agents.
-/

def efx_no_self_three_split_code (r : Fin 6) (q : Fin 9 → Fin 4) : Fin 13 → Fin 4 := (![![q 0, q 0, q 0, q 1, q 1, q 1, q 2, q 3, q 4, q 5, q 6, q 7, q 8], ![q 0, q 0, q 0, q 1, q 2, q 3, q 4, q 4, q 4, q 5, q 6, q 7, q 8], ![q 0, q 0, q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7, q 7, q 7, q 8], ![q 0, q 1, q 2, q 3, q 3, q 3, q 4, q 4, q 4, q 5, q 6, q 7, q 8], ![q 0, q 1, q 2, q 3, q 3, q 3, q 4, q 5, q 6, q 7, q 7, q 7, q 8], ![q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 6, q 6, q 7, q 7, q 7, q 8]] : Fin 6 → Fin 13 → Fin 4) r
