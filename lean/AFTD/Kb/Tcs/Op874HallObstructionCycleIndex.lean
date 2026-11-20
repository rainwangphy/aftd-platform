import AFTD.Prelude

/-!
# op874_hall_obstruction_cycle_index

Topic: graphs   Node: a470f57e0511

Provenance: helper lemma. Explicit paired-odd-cycle interaction obstruction in OP-874, experiment 35342.

The prescribed cycle index of each of the forty vertices.
-/

def op874_hall_obstruction_cycle_index (v : Fin 40) : Fin 8 := if v.val < 3 then 0 else if v.val < 6 then 1 else if v.val < 9 then 2 else if v.val < 20 then 3 else if v.val < 31 then 4 else if v.val < 34 then 5 else if v.val < 37 then 6 else 7
