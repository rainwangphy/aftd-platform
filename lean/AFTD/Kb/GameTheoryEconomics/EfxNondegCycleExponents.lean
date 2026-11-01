import AFTD.Prelude

/-!
# efx_nondeg_cycle_exponents

Topic: fair_division   Node: 39d59cbd128b

Provenance: helper lemma. Nondegenerate three-source champion two-cycle exchange obstruction for OP-7, experiments 11481–11487; related arXiv:2002.05119 Section 3.1.

The four explicit binary exponent rows, each a permutation of 0 through 12.
-/

def efx_nondeg_cycle_exponents : Fin 4 → Fin 13 → ℕ := ![![5,11,4,3,10,6,9,8,7,12,0,1,2], ![2,3,1,8,12,10,9,0,11,5,4,7,6], ![2,4,5,10,6,9,3,11,8,7,12,0,1], ![7,5,9,0,2,1,4,11,3,12,8,10,6]]
