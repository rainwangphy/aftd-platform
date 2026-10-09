import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteLinkTemplateThreeGraph

/-!
# bipartite_link_template_three_graph_card

Topic: combinatorics   Node: df7c3d166d63

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.11642 (A counterexample to the bipartite-link conjecture for 3-graphs).

The template 3-graph has 24 edges.
-/

theorem bipartite_link_template_three_graph_card : bipartite_link_template_three_graph.card = 24 := by
  decide
