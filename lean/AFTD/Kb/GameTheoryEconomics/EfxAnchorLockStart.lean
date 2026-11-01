import AFTD.Prelude

/-!
# efx_anchor_lock_start

Topic: fair_division   Node: 98f2dafcbb69

Provenance: helper lemma. Nondegenerate no-singleton four-agent Pareto-maximal partial EFX obstruction, experiments 11500–11507; locked-good lift of arXiv:2002.05119 Section 5.

The partial starting allocation, with owner 4 denoting the unallocated good 6; its four bundle sizes are 4,3,2,2.
-/

def efx_anchor_lock_start : Fin 12 → Fin 5 := ![(1 : Fin 5),0,0,0,1,2,4,1,2,0,3,3]
