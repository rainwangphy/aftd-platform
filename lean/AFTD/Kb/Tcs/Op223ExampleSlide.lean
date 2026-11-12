import AFTD.Prelude
import AFTD.Kb.Tcs.Op223ExampleGraph

/-!
# op223_example_slide

Topic: graphs   Node: 615e38ed6a7f

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; exact experiment 22883

Replace edge 4-b by 5-b in the eight-vertex example.
-/

def op223_example_slide (b : Fin 8) : SimpleGraph (Fin 8) :=
  op223_example_graph.deleteEdges {s(4,b)} ⊔ SimpleGraph.fromEdgeSet {s(5,b)}
