import AFTD.Prelude

/-!
# efx_allsource_pair_code

Topic: fair_division   Node: 7ac8881130af

Provenance: helper lemma. Three-valued all-source no-self two-split EFX obstruction for OP-7; experiments 11638–11642.

Encode all complete owner functions splitting at most pair j, with q 5 the charity owner.
-/

def efx_allsource_pair_code (j : Fin 4) (q : Fin 6 → Fin 4) : Fin 9 → Fin 4 := ![q 0, if j = 0 then q 4 else q 0, q 1, if j = 1 then q 4 else q 1,
  q 2, if j = 2 then q 4 else q 2, q 3, if j = 3 then q 4 else q 3, q 5]
