import AFTD.Prelude

/-!
# op874_hall_obstruction_factor_edges

Topic: graphs   Node: dbbe65e07520

Provenance: helper lemma. Explicit paired-odd-cycle interaction obstruction in OP-874, experiment 35342.

The explicit forty cycle edges in the prescribed factor.
-/

def op874_hall_obstruction_factor_edges : Finset (Sym2 (Fin 40)) := {s((0 : Fin 40), (1 : Fin 40)), s((1 : Fin 40), (2 : Fin 40)), s((2 : Fin 40), (0 : Fin 40)), s((3 : Fin 40), (4 : Fin 40)), s((4 : Fin 40), (5 : Fin 40)), s((5 : Fin 40), (3 : Fin 40)), s((6 : Fin 40), (7 : Fin 40)), s((7 : Fin 40), (8 : Fin 40)), s((8 : Fin 40), (6 : Fin 40)), s((9 : Fin 40), (10 : Fin 40)), s((10 : Fin 40), (11 : Fin 40)), s((11 : Fin 40), (12 : Fin 40)), s((12 : Fin 40), (13 : Fin 40)), s((13 : Fin 40), (14 : Fin 40)), s((14 : Fin 40), (15 : Fin 40)), s((15 : Fin 40), (16 : Fin 40)), s((16 : Fin 40), (17 : Fin 40)), s((17 : Fin 40), (18 : Fin 40)), s((18 : Fin 40), (19 : Fin 40)), s((19 : Fin 40), (9 : Fin 40)), s((20 : Fin 40), (21 : Fin 40)), s((21 : Fin 40), (22 : Fin 40)), s((22 : Fin 40), (23 : Fin 40)), s((23 : Fin 40), (24 : Fin 40)), s((24 : Fin 40), (25 : Fin 40)), s((25 : Fin 40), (26 : Fin 40)), s((26 : Fin 40), (27 : Fin 40)), s((27 : Fin 40), (28 : Fin 40)), s((28 : Fin 40), (29 : Fin 40)), s((29 : Fin 40), (30 : Fin 40)), s((30 : Fin 40), (20 : Fin 40)), s((31 : Fin 40), (32 : Fin 40)), s((32 : Fin 40), (33 : Fin 40)), s((33 : Fin 40), (31 : Fin 40)), s((34 : Fin 40), (35 : Fin 40)), s((35 : Fin 40), (36 : Fin 40)), s((36 : Fin 40), (34 : Fin 40)), s((37 : Fin 40), (38 : Fin 40)), s((38 : Fin 40), (39 : Fin 40)), s((39 : Fin 40), (37 : Fin 40))}
