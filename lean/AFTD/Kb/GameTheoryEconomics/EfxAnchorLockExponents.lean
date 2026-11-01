import AFTD.Prelude

/-!
# efx_anchor_lock_exponents

Topic: fair_division   Node: 683986465fbc

Provenance: helper lemma. Nondegenerate no-singleton four-agent Pareto-maximal partial EFX obstruction, experiments 11500–11507; locked-good lift of arXiv:2002.05119 Section 5.

The four binary exponent rows, each a permutation of 0 through 11.
-/

def efx_anchor_lock_exponents : Fin 4 → Fin 12 → ℕ := ![![0,1,2,3,4,5,6,7,8,9,10,11], ![4,5,6,7,8,9,10,11,0,1,2,3], ![8,9,10,11,0,1,2,3,4,5,6,7], ![2,3,4,5,6,7,8,9,10,11,0,1]]
