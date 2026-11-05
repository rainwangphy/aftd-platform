import AFTD.Prelude

/-!
# maxcut_defect_two_escape_graph

Topic: equilibria   Node: 854784014efc

Provenance: helper lemma. Explicit graph in experiments 16322–16323.

The 15-vertex graph used for an equal-cut strong deviation from a defect-two Nash coloring.
-/

def maxcut_defect_two_escape_graph : SimpleGraph (Fin 15) := SimpleGraph.fromRel (fun (u v : Fin 15) => (u.val, v.val) ∈ [(0,1), (0,3), (0,4), (0,8), (0,13), (0,14), (1,2), (1,5), (1,9), (1,13), (1,14), (2,3), (2,6), (2,10), (2,13), (2,14), (3,7), (3,11), (3,13), (3,14), (4,5), (4,7), (4,8), (4,12), (4,14), (5,6), (5,9), (5,12), (5,14), (6,7), (6,10), (6,12), (6,14), (7,11), (7,12), (7,14), (8,9), (8,11), (8,12), (8,13), (9,10), (9,12), (9,13), (10,11), (10,12), (10,13), (11,12), (11,13)])
