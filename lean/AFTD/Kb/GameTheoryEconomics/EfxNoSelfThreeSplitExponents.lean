import AFTD.Prelude

/-!
# efx_no_self_three_split_exponents

Topic: fair_division   Node: d2c9c529ada6

Provenance: helper lemma. Nondegenerate strengthening of the OP-7 no-self three-split obstruction, experiments 11492–11494; related perturbation argument arXiv:2002.05119 Lemma 1.

For each agent, the exponents 10,11,12 belong to her old triple in order; exponents 0 through 9 belong in order to all remaining goods.
-/

def efx_no_self_three_split_exponents : Fin 4 → Fin 13 → ℕ := ![![10,11,12,0,1,2,3,4,5,6,7,8,9], ![0,1,2,10,11,12,3,4,5,6,7,8,9], ![0,1,2,3,4,5,10,11,12,6,7,8,9], ![0,1,2,3,4,5,6,7,8,10,11,12,9]]
