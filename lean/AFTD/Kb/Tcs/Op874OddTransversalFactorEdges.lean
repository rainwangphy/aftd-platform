import AFTD.Prelude

/-!
# op874_odd_transversal_factor_edges

Topic: graphs   Node: 407e7cd66b3c

Provenance: helper lemma. Explicit one-sided nonadjacent-defect obstruction adapted from https://arxiv.org/html/2309.12150 section 2.2, experiment 35359.

The edges of three seven-cycles and seven triangles.
-/

def op874_odd_transversal_factor_edges : Finset (Sym2 (Fin 42)) := {s((0 : Fin 42), (1 : Fin 42)), s((1 : Fin 42), (2 : Fin 42)), s((2 : Fin 42), (3 : Fin 42)), s((3 : Fin 42), (4 : Fin 42)), s((4 : Fin 42), (5 : Fin 42)), s((5 : Fin 42), (6 : Fin 42)), s((6 : Fin 42), (0 : Fin 42)), s((7 : Fin 42), (8 : Fin 42)), s((8 : Fin 42), (9 : Fin 42)), s((9 : Fin 42), (10 : Fin 42)), s((10 : Fin 42), (11 : Fin 42)), s((11 : Fin 42), (12 : Fin 42)), s((12 : Fin 42), (13 : Fin 42)), s((13 : Fin 42), (7 : Fin 42)), s((14 : Fin 42), (15 : Fin 42)), s((15 : Fin 42), (16 : Fin 42)), s((16 : Fin 42), (17 : Fin 42)), s((17 : Fin 42), (18 : Fin 42)), s((18 : Fin 42), (19 : Fin 42)), s((19 : Fin 42), (20 : Fin 42)), s((20 : Fin 42), (14 : Fin 42)), s((21 : Fin 42), (22 : Fin 42)), s((22 : Fin 42), (23 : Fin 42)), s((23 : Fin 42), (21 : Fin 42)), s((24 : Fin 42), (25 : Fin 42)), s((25 : Fin 42), (26 : Fin 42)), s((26 : Fin 42), (24 : Fin 42)), s((27 : Fin 42), (28 : Fin 42)), s((28 : Fin 42), (29 : Fin 42)), s((29 : Fin 42), (27 : Fin 42)), s((30 : Fin 42), (31 : Fin 42)), s((31 : Fin 42), (32 : Fin 42)), s((32 : Fin 42), (30 : Fin 42)), s((33 : Fin 42), (34 : Fin 42)), s((34 : Fin 42), (35 : Fin 42)), s((35 : Fin 42), (33 : Fin 42)), s((36 : Fin 42), (37 : Fin 42)), s((37 : Fin 42), (38 : Fin 42)), s((38 : Fin 42), (36 : Fin 42)), s((39 : Fin 42), (40 : Fin 42)), s((40 : Fin 42), (41 : Fin 42)), s((41 : Fin 42), (39 : Fin 42))}
