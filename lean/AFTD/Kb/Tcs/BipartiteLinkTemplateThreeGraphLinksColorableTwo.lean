import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeGraphLink
import AFTD.Kb.Tcs.BipartiteLinkTemplateThreeGraph
import AFTD.Kb.Tcs.ThreeGraphLinkAdjIff

/-!
# bipartite_link_template_three_graph_links_colorable_two

Topic: combinatorics   Node: ada390ba4b19

Provenance: formalization of a published result. Source: arXiv:2610.11642 (A counterexample to the bipartite-link conjecture for 3-graphs), Lemma 2.1.

Every vertex link graph of the 9-vertex template 3-graph is bipartite (2-colorable).
-/

def bipartite_link_template_three_graph_links_colorable_two_part (i : Fin 9) : Finset (Fin 9) :=
  match i with
  | 0 => {1, 3, 6, 8}
  | 1 => {0, 3, 8}
  | 2 => {0, 1, 4, 5, 7}
  | 3 => {0, 2, 5, 6, 7, 8}
  | 4 => {0, 2, 5, 6, 7, 8}
  | 5 => {0, 1, 2, 4, 7}
  | 6 => {0, 3, 5, 8}
  | 7 => {0, 3, 8}
  | 8 => {0, 1, 3, 7}

def bipartite_link_template_three_graph_links_colorable_two_coloring (i : Fin 9) : Fin 9 → Fin 2 :=
  fun j => if j ∈ bipartite_link_template_three_graph_links_colorable_two_part i then 0 else 1

lemma bipartite_link_template_three_graph_links_colorable_two_valid :
    ∀ (i j k : Fin 9),
      (three_graph_link bipartite_link_template_three_graph i).Adj j k →
      bipartite_link_template_three_graph_links_colorable_two_coloring i j ≠
        bipartite_link_template_three_graph_links_colorable_two_coloring i k := by
  dsimp [three_graph_link, SimpleGraph.fromRel,
    bipartite_link_template_three_graph_links_colorable_two_coloring,
    bipartite_link_template_three_graph_links_colorable_two_part]
  decide

theorem bipartite_link_template_three_graph_links_colorable_two (i : Fin 9) :
    (three_graph_link bipartite_link_template_three_graph i).Colorable 2 := ⟨SimpleGraph.Coloring.mk (bipartite_link_template_three_graph_links_colorable_two_coloring i)
    (fun {j k} => bipartite_link_template_three_graph_links_colorable_two_valid i j k)⟩
