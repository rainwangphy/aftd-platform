import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphOfEdgeList

/-!
# op_1239_candidate36

Topic: combinatorics   Node: 09dcdac598f2

Provenance: helper lemma. Candidate for OP-1239; computations 28328 and 28332 checks the standard leaf-deletion recurrence from arXiv:2611.07503, Lemma 1.

The simple graph on the 36 vertices Fin 36 with the 35 undirected edges listed in its definition.
-/

/-- The explicit 36-vertex candidate for a maximum-degree-three tree with a non-log-concave partial Petrial polynomial. -/
def op_1239_candidate36 : SimpleGraph (Fin 36) := simple_graph_of_edge_list [(0, 1), (0, 3), (0, 8), (1, 2), (1, 4), (2, 6), (2, 7), (3, 5), (3, 21), (4, 12), (4, 16), (5, 13), (5, 14), (6, 9), (6, 18), (7, 10), (7, 15), (8, 11), (8, 26), (10, 19), (10, 30), (11, 27), (11, 33), (12, 22), (13, 17), (14, 24), (16, 20), (16, 31), (18, 29), (18, 32), (20, 23), (20, 28), (23, 25), (28, 34), (29, 35)]
