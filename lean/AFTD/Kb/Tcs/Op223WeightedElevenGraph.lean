import AFTD.Prelude

/-!
# op223_weighted_eleven_graph

Topic: graphs   Node: ea83304dc9d1

Provenance: helper lemma. The eleven-vertex rational weighted-shift candidate.

The eleven-vertex support tree of the rational weighted-shift candidate.
-/

def op223_weighted_eleven_graph : SimpleGraph (Fin 11) := SimpleGraph.fromEdgeSet {s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(0,6), s(0,7), s(7,8), s(8,9), s(0,10)}
