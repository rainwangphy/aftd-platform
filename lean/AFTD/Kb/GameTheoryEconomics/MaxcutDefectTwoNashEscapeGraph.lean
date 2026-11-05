import AFTD.Prelude

/-!
# maxcut_defect_two_nash_escape_graph

Topic: equilibria   Node: 6547ceacb617

Provenance: helper lemma. Explicit graph in independently checked experiments 16337–16338.

The 27-vertex graph for a Nash-to-Nash equal-welfare strong deviation escaping defect two.
-/

def maxcut_defect_two_nash_escape_graph : SimpleGraph (Fin 27) := SimpleGraph.fromRel (fun (u v : Fin 27) => (u.val, v.val) ∈ [(0,1), (0,3), (0,4), (0,8), (0,13), (0,14), (1,2), (1,5), (1,9), (1,13), (1,14), (2,3), (2,6), (2,10), (2,13), (2,14), (3,7), (3,11), (3,13), (3,14), (4,5), (4,7), (4,8), (4,12), (4,14), (5,6), (5,9), (5,12), (5,14), (6,7), (6,10), (6,12), (6,14), (7,11), (7,12), (7,14), (8,9), (8,11), (8,12), (8,13), (9,10), (9,12), (9,13), (10,11), (10,12), (10,13), (11,12), (11,13), (12,15), (12,16), (12,17), (12,18), (13,19), (13,20), (13,21), (13,22), (14,23), (14,24), (14,25), (14,26)])
