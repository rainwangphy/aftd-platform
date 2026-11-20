import AFTD.Prelude

/-!
# op874_odd_transversal_matching

Topic: graphs   Node: 1395618013ec

Provenance: helper lemma. Explicit one-sided nonadjacent-defect obstruction adapted from https://arxiv.org/html/2309.12150 section 2.2, experiment 35359.

The matching encoded by the seven triples of the independent-transversal obstruction.
-/

def op874_odd_transversal_matching : Finset (Sym2 (Fin 42)) := {s((0 : Fin 42), (21 : Fin 42)), s((2 : Fin 42), (22 : Fin 42)), s((5 : Fin 42), (23 : Fin 42)), s((7 : Fin 42), (24 : Fin 42)), s((9 : Fin 42), (25 : Fin 42)), s((12 : Fin 42), (26 : Fin 42)), s((14 : Fin 42), (27 : Fin 42)), s((16 : Fin 42), (28 : Fin 42)), s((19 : Fin 42), (29 : Fin 42)), s((1 : Fin 42), (30 : Fin 42)), s((11 : Fin 42), (31 : Fin 42)), s((13 : Fin 42), (32 : Fin 42)), s((4 : Fin 42), (33 : Fin 42)), s((18 : Fin 42), (34 : Fin 42)), s((20 : Fin 42), (35 : Fin 42)), s((3 : Fin 42), (36 : Fin 42)), s((8 : Fin 42), (37 : Fin 42)), s((10 : Fin 42), (38 : Fin 42)), s((6 : Fin 42), (39 : Fin 42)), s((15 : Fin 42), (40 : Fin 42)), s((17 : Fin 42), (41 : Fin 42))}
