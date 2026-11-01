import AFTD.Prelude

/-!
# efx_pareto_three_start

Topic: fair_division   Node: 340e8d4b08f7

Provenance: helper lemma. Iterated two-lock source lift of the three-agent partial EFX Pareto barrier; experiment 11578.

The base partial allocation with good 6 unallocated.
-/

def efx_pareto_three_start : Fin 7 → Fin 4 := ![(1 : Fin 4),0,0,0,1,2,3]
