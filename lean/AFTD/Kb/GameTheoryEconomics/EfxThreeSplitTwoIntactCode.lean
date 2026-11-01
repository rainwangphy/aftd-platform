import AFTD.Prelude

/-!
# efx_three_split_two_intact_code

Topic: fair_division   Node: 826e43a47e05

Provenance: helper lemma. Finite equal-pair obstruction to OP-7 completion routes, experiments 11408, 11409, 11411, 11412.

The index r selects one of the six pairs of old adjacent pairs to keep intact, and q assigns the two intact pairs, the four remaining old goods, and the last good to agents. The order of selected old-pair indices is (0,1), (0,2), (0,3), (1,2), (1,3), (2,3).
-/

def efx_three_split_two_intact_code (r : Fin 6) (q : Fin 7 → Fin 4) : Fin 9 → Fin 4 := (![![q 0,q 0,q 1,q 1,q 2,q 3,q 4,q 5,q 6], ![q 0,q 0,q 1,q 2,q 3,q 3,q 4,q 5,q 6], ![q 0,q 0,q 1,q 2,q 3,q 4,q 5,q 5,q 6], ![q 0,q 1,q 2,q 2,q 3,q 3,q 4,q 5,q 6], ![q 0,q 1,q 2,q 2,q 3,q 4,q 5,q 5,q 6], ![q 0,q 1,q 2,q 3,q 4,q 4,q 5,q 5,q 6]] : Fin 6 → Fin 9 → Fin 4) r
