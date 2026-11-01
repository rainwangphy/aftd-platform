import AFTD.Prelude

/-!
# efx_source_two_witness

Topic: fair_division   Node: 3a14bf442b70

Provenance: helper lemma. Nine-good isolated-source completion obstruction derived from the three-agent partial Pareto barrier in arXiv:2002.05119, Section 5; experiments 11561–11562.

A complete EFX allocation witness.
-/

def efx_source_two_witness : Fin 9 → Fin 4 := ![(0 : Fin 4),0,0,0,1,2,0,1,3]
