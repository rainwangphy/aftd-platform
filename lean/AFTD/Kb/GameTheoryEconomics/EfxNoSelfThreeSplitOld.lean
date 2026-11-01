import AFTD.Prelude

/-!
# efx_no_self_three_split_old

Topic: fair_division   Node: 6450c32d6e39

Provenance: helper lemma. Positive equal-triple no-self-champion obstruction to the OP-7 two-bundle exchange route, experiments 11462–11471.

The old partial allocation consists of four consecutive triples; good 12 is unallocated.
-/

def efx_no_self_three_split_old : Fin 4 → Finset (Fin 13) := ![{0,1,2}, {3,4,5}, {6,7,8}, {9,10,11}]
