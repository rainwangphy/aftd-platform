import AFTD.Prelude

/-!
# efx_min_cycle_values

Topic: fair_division   Node: 54a862b8222e

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

The four rows of the positive natural valuation matrix are (3,3,12,2,15,1,1,1,16,16,1,1,3), (3,14,1,3,3,12,16,1,1,1,1,16,3), (2,2,32,6,2,28,2,32,2,2,19,15,2), and (1,16,1,3,3,12,14,1,3,16,1,1,1).
-/

def efx_min_cycle_values : Fin 4 → Fin 13 → ℕ := ![![3,3,12,2,15,1,1,1,16,16,1,1,3], ![3,14,1,3,3,12,16,1,1,1,1,16,3], ![2,2,32,6,2,28,2,32,2,2,19,15,2], ![1,16,1,3,3,12,14,1,3,16,1,1,1]]
