import AFTD.Prelude

/-!
# op223_example_graph

Topic: graphs   Node: 7da1c1adda8e

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; exact experiment 22883

The eight-vertex tree with edges 01, 04, 07, 12, 23, 45 and 46.
-/

def op223_example_graph : SimpleGraph (Fin 8) :=
  SimpleGraph.fromEdgeSet {s(0,1), s(0,4), s(0,7), s(1,2), s(2,3), s(4,5), s(4,6)}
