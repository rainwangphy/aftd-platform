import AFTD.Prelude

/-!
# op223_weighted_support_graph

Topic: graphs   Node: 843ef6fb4d78

Provenance: helper lemma. The finite weighted-shift counterexample candidate.

The thirteen-vertex tree obtained by deleting the pendant edge from the rational weighted-shift candidate.
-/

def op223_weighted_support_graph : SimpleGraph (Fin 13) :=
  SimpleGraph.fromEdgeSet {s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(0,6), s(0,7), s(7,8), s(8,9), s(9,10), s(10,11), s(11,12)}
