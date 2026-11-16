import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphOfEdgeList

/-!
# op_1239_candidate31

Topic: combinatorics   Node: b016ee34fcb2

Provenance: helper lemma. OP-1239, arXiv:2611.07503, Problem 16; candidate from experiments 28663 and 28669.

The simple graph on Fin 31 whose edges are the thirty pairs listed in its definition.
-/

def op_1239_candidate31 : SimpleGraph (Fin 31) := simple_graph_of_edge_list [(0, 1), (0, 11), (0, 21), (1, 2), (1, 4), (2, 3), (4, 5), (4, 6), (6, 7), (6, 9), (7, 8), (9, 10), (11, 12), (11, 14), (12, 13), (14, 15), (14, 16), (16, 17), (16, 19), (17, 18), (19, 20), (21, 22), (21, 24), (22, 23), (24, 25), (24, 26), (26, 27), (26, 29), (27, 28), (29, 30)]
