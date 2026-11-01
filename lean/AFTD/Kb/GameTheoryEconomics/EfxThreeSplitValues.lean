import AFTD.Prelude

/-!
# efx_three_split_values

Topic: fair_division   Node: 297712a3ffa0

Provenance: helper lemma. Finite equal-pair obstruction to OP-7 completion routes, experiments 11408, 11409, 11411, 11412.

The natural-valued four-agent nine-good matrix with rows (3,14,3,14,1,16,4,13,5), (1,5,5,1,5,1,2,4,3), (14,3,16,1,3,14,4,13,5), and (8,1,1,8,8,1,3,6,4). Old goods are adjacent pairs (0,1), (2,3), (4,5), (6,7), and good 8 is the unallocated good.
-/

def efx_three_split_values : Fin 4 → Fin 9 → ℕ := ![![3,14,3,14,1,16,4,13,5], ![1,5,5,1,5,1,2,4,3], ![14,3,16,1,3,14,4,13,5], ![8,1,1,8,8,1,3,6,4]]
