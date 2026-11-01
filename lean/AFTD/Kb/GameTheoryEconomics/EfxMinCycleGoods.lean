import AFTD.Prelude

/-!
# efx_min_cycle_goods

Topic: fair_division   Node: 6bfafb7b8fcf

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

For each target old bundle, list its three goods followed by the unallocated good.
-/

def efx_min_cycle_goods : Fin 4 → Fin 4 → Fin 13 := ![![0,1,2,12], ![3,4,5,12], ![6,7,8,12], ![9,10,11,12]]
