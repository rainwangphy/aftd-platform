import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeGraphLink
import AFTD.Kb.Tcs.BipartiteLinkTemplateThreeGraph
import AFTD.Kb.Tcs.ThreeGraphLinkAdjIff

/-!
# three_graph_link_template_zero_adj

Topic: combinatorics   Node: 744f5595cc82

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.11642 (A counterexample to the bipartite-link conjecture for 3-graphs).

In the template, 1 and 4 are adjacent in the link of 0 (since {0, 1, 4} is an edge).
-/

theorem three_graph_link_template_zero_adj :
    (three_graph_link bipartite_link_template_three_graph 0).Adj 1 4 := by
  rw [three_graph_link_adj_iff]; decide
