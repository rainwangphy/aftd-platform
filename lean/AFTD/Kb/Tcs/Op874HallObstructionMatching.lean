import AFTD.Prelude

/-!
# op874_hall_obstruction_matching

Topic: graphs   Node: 5b4f10c7c609

Provenance: helper lemma. Explicit paired-odd-cycle interaction obstruction in OP-874, experiment 35342.

The explicit twenty matching edges joining those cycles.
-/

def op874_hall_obstruction_matching : Finset (Sym2 (Fin 40)) := {s((0 : Fin 40), (20 : Fin 40)), s((1 : Fin 40), (21 : Fin 40)), s((2 : Fin 40), (22 : Fin 40)), s((3 : Fin 40), (23 : Fin 40)), s((4 : Fin 40), (24 : Fin 40)), s((5 : Fin 40), (25 : Fin 40)), s((6 : Fin 40), (26 : Fin 40)), s((7 : Fin 40), (27 : Fin 40)), s((8 : Fin 40), (28 : Fin 40)), s((9 : Fin 40), (29 : Fin 40)), s((10 : Fin 40), (30 : Fin 40)), s((11 : Fin 40), (31 : Fin 40)), s((12 : Fin 40), (32 : Fin 40)), s((13 : Fin 40), (33 : Fin 40)), s((14 : Fin 40), (34 : Fin 40)), s((15 : Fin 40), (35 : Fin 40)), s((16 : Fin 40), (36 : Fin 40)), s((17 : Fin 40), (37 : Fin 40)), s((18 : Fin 40), (38 : Fin 40)), s((19 : Fin 40), (39 : Fin 40))}
