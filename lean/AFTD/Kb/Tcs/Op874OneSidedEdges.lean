import AFTD.Prelude

/-!
# op874_one_sided_edges

Topic: graphs   Node: ee2d1dd9c3e2

Provenance: helper lemma. Explicit fixed-factor orientation obstruction, experiments 35726–35727.

The cycle and matching edges of the explicit 36-vertex graph.
-/

def op874_one_sided_edges : Finset (Sym2 (Fin 36)) := {s((0 : Fin 36), (1 : Fin 36)), s((1 : Fin 36), (2 : Fin 36)), s((2 : Fin 36), (3 : Fin 36)), s((3 : Fin 36), (4 : Fin 36)), s((4 : Fin 36), (5 : Fin 36)), s((5 : Fin 36), (6 : Fin 36)), s((6 : Fin 36), (7 : Fin 36)), s((7 : Fin 36), (8 : Fin 36)), s((8 : Fin 36), (9 : Fin 36)), s((9 : Fin 36), (10 : Fin 36)), s((10 : Fin 36), (0 : Fin 36)), s((11 : Fin 36), (12 : Fin 36)), s((12 : Fin 36), (13 : Fin 36)), s((13 : Fin 36), (14 : Fin 36)), s((14 : Fin 36), (15 : Fin 36)), s((15 : Fin 36), (16 : Fin 36)), s((16 : Fin 36), (17 : Fin 36)), s((17 : Fin 36), (11 : Fin 36)), s((18 : Fin 36), (19 : Fin 36)), s((19 : Fin 36), (20 : Fin 36)), s((20 : Fin 36), (21 : Fin 36)), s((21 : Fin 36), (22 : Fin 36)), s((22 : Fin 36), (18 : Fin 36)), s((23 : Fin 36), (24 : Fin 36)), s((24 : Fin 36), (25 : Fin 36)), s((25 : Fin 36), (26 : Fin 36)), s((26 : Fin 36), (27 : Fin 36)), s((27 : Fin 36), (23 : Fin 36)), s((28 : Fin 36), (29 : Fin 36)), s((29 : Fin 36), (30 : Fin 36)), s((30 : Fin 36), (28 : Fin 36)), s((31 : Fin 36), (32 : Fin 36)), s((32 : Fin 36), (33 : Fin 36)), s((33 : Fin 36), (34 : Fin 36)), s((34 : Fin 36), (35 : Fin 36)), s((35 : Fin 36), (31 : Fin 36)), s((8 : Fin 36), (19 : Fin 36)), s((11 : Fin 36), (26 : Fin 36)), s((16 : Fin 36), (31 : Fin 36)), s((14 : Fin 36), (20 : Fin 36)), s((6 : Fin 36), (27 : Fin 36)), s((9 : Fin 36), (23 : Fin 36)), s((12 : Fin 36), (33 : Fin 36)), s((15 : Fin 36), (24 : Fin 36)), s((17 : Fin 36), (18 : Fin 36)), s((4 : Fin 36), (30 : Fin 36)), s((13 : Fin 36), (22 : Fin 36)), s((1 : Fin 36), (28 : Fin 36)), s((2 : Fin 36), (29 : Fin 36)), s((0 : Fin 36), (32 : Fin 36)), s((10 : Fin 36), (35 : Fin 36)), s((3 : Fin 36), (25 : Fin 36)), s((5 : Fin 36), (21 : Fin 36)), s((7 : Fin 36), (34 : Fin 36))}
