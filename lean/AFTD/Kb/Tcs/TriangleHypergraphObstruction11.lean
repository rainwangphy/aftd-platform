import AFTD.Prelude

/-!
# triangle_hypergraph_obstruction11

Topic: graphs   Node: 6b2ed8daea15

Provenance: helper lemma. Experiment 13111 for the triangle packing-cover campaign.

An explicit eleven-point eleven-triple linear degree-three system arising as a counterexample to a proposed hypergraph extension of triangle packing-covering.
-/

def triangle_hypergraph_obstruction11 : List (Finset (Fin 11)) := [{0,1,2}, {3,4,5}, {0,3,8}, {0,4,7}, {1,6,9}, {1,8,10},
   {2,4,8}, {2,6,10}, {3,7,9}, {5,6,7}, {5,9,10}]
