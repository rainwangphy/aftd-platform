import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# simple_graph_is_rich_neighbor_coloring_of_forall_rich

Topic: graphs   Node: 753636d13917

Provenance: helper lemma. Sanity lemma, arXiv:2610.21868 (Rich-neighbor 5-edge-colorings of subcubic graphs whose 3-vertices induce a matching), Sec. 1 (rich-neighbor colouring relaxes strong edge colouring).

A proper edge colouring in which every edge is rich (for instance a strong edge colouring) is a rich-neighbor edge colouring.
-/

theorem simple_graph_is_rich_neighbor_coloring_of_forall_rich {V α : Type*} (G : SimpleGraph V)
    (c : G.lineGraph.Coloring α) (h : ∀ e, simple_graph_edge_is_rich G c e) :
    simple_graph_is_rich_neighbor_coloring G c :=
  fun _ ⟨f, hf⟩ => ⟨f, hf, h f⟩
