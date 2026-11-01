import AFTD.Prelude

/-!
# efx_source_two_start

Topic: fair_division   Node: 2e5c371ecfc0

Provenance: helper lemma. Nine-good isolated-source completion obstruction derived from the three-agent partial Pareto barrier in arXiv:2002.05119, Section 5; experiments 11561–11562.

The initial old-good allocation, with both locks at agent 3 and good 6 unallocated.
-/

def efx_source_two_start : Fin 9 → Fin 5 := ![(1 : Fin 5),0,0,0,1,2,4,3,3]
