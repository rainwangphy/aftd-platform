import AFTD.Prelude

/-!
# bipartite_link_template_three_graph

Topic: combinatorics   Node: ba00106db235

Provenance: formalization of a published result. Source: arXiv:2610.11642 (A counterexample to the bipartite-link conjecture for 3-graphs), (2.1) (the template 3-graph F of the construction).

The 9-vertex template 3-graph on {0, …, 8} with the 24 triples listed in (2.1).
-/

/-- The 9-vertex template 3-graph of arXiv:2610.11642, (2.1): 24 triples on `{0, …, 8}`. -/
def bipartite_link_template_three_graph : Finset (Finset (Fin 9)) :=
  {{0, 1, 4}, {0, 1, 7}, {0, 2, 6}, {0, 2, 8}, {0, 3, 4}, {0, 5, 8}, {0, 6, 7}, {1, 2, 3},
   {1, 2, 8}, {1, 3, 5}, {1, 3, 6}, {1, 3, 7}, {1, 4, 8}, {1, 5, 8}, {1, 6, 8}, {2, 3, 4},
   {2, 5, 6}, {2, 7, 8}, {3, 4, 5}, {3, 4, 6}, {3, 4, 7}, {3, 4, 8}, {5, 7, 8}, {6, 7, 8}}
