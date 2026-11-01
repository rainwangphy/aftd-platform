import AFTD.Prelude

/-!
# efx_min_cycle_outcome

Topic: fair_division   Node: a1f221a9b173

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

The six outcomes obtained from the two inclusion-minimal two-cycles: for each chosen pair of upper halves, mode 0 swaps them, mode 1 additionally replaces the first lower half by good 12, and mode 2 instead replaces the second lower half by good 12.
-/

def efx_min_cycle_outcome : Fin 2 → Fin 3 → Fin 4 → Finset (Fin 13) := ![![![{2,3,4}, {0,1,5}, {6,7,8}, {9,10,11}], ![{3,4,12}, {0,1,5}, {6,7,8}, {9,10,11}], ![{2,3,4}, {0,1,12}, {6,7,8}, {9,10,11}]], ![![{2,4,5}, {0,1,3}, {6,7,8}, {9,10,11}], ![{4,5,12}, {0,1,3}, {6,7,8}, {9,10,11}], ![{2,4,5}, {0,1,12}, {6,7,8}, {9,10,11}]]]
