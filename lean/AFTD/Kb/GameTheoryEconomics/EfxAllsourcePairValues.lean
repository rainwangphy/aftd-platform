import AFTD.Prelude

/-!
# efx_allsource_pair_values

Topic: fair_division   Node: 8313bd7ff590

Provenance: helper lemma. Three-valued all-source no-self two-split EFX obstruction for OP-7; experiments 11638–11642.

Three-valued positive four-agent values for four old pairs and one charity good.
-/

def efx_allsource_pair_values : Fin 4 → Fin 9 → ℕ := ![![2,2,1,3,1,3,1,3,2], ![3,1,2,2,3,1,1,3,2], ![1,3,3,1,1,3,2,2,1], ![3,1,3,1,3,1,2,2,2]]
