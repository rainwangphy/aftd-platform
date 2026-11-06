import AFTD.Prelude

/-!
# maxcut_nash_pivot_obstruction_graph

Topic: equilibria   Node: 74c589248697

Provenance: helper lemma. Finite atlas enumeration in experiment 16715.

A six-vertex unweighted graph testing vertex extension under Nash stability.
-/

def maxcut_nash_pivot_obstruction_graph : SimpleGraph (Fin 6) := SimpleGraph.fromRel (fun u v : Fin 6 => (u.val, v.val) ∈ [(0, 2), (1, 2), (1, 3), (1, 4), (2, 3), (2, 5), (3, 4), (3, 5), (4, 5)])
