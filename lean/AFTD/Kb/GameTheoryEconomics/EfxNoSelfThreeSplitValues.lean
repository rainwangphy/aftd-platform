import AFTD.Prelude

/-!
# efx_no_self_three_split_values

Topic: fair_division   Node: 510043fc15fa

Provenance: helper lemma. Positive equal-triple no-self-champion obstruction to the OP-7 two-bundle exchange route, experiments 11462–11471.

The positive natural-valued matrix with rows (3,23,43,1,38,30,35,1,33,2,47,20,3), (1,25,44,40,9,21,1,41,28,34,1,35,3), (19,1,31,29,1,21,9,29,13,1,25,25,2), and (18,7,12,3,33,1,28,1,8,22,13,2,2).
-/

def efx_no_self_three_split_values : Fin 4 → Fin 13 → ℕ := ![![3,23,43,1,38,30,35,1,33,2,47,20,3], ![1,25,44,40,9,21,1,41,28,34,1,35,3], ![19,1,31,29,1,21,9,29,13,1,25,25,2], ![18,7,12,3,33,1,28,1,8,22,13,2,2]]
