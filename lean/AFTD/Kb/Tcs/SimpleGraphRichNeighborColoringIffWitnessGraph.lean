import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRichWitnessGraphColoringIff
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SimpleGraphRichWitnessGraph
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# simple_graph_rich_neighbor_coloring_iff_witness_graph

Topic: graphs   Node: 8172fc99408c

Provenance: helper lemma. Helper for OP-309, using arXiv:2610.16446, Section 2, Lemmas 3 and 4. Total domination is stated directly in the line graph; the converse chooses all rich edges.

G has a rich-neighbor coloring with palette alpha exactly when some R totally dominates the non-isolated vertices of the line graph and its prescribed-witness graph is alpha-colorable.
-/

theorem simple_graph_rich_neighbor_coloring_iff_witness_graph
    {V α : Type*} (G : SimpleGraph V) :
    (∃ c : G.lineGraph.Coloring α, simple_graph_is_rich_neighbor_coloring G c) ↔
    ∃ R : Set G.edgeSet,
      (∀ e, (∃ f, G.lineGraph.Adj e f) → ∃ r ∈ R, G.lineGraph.Adj e r) ∧
      Nonempty ((simple_graph_rich_witness_graph G R).Coloring α) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨{r | simple_graph_edge_is_rich G c r}, ?_, ?_⟩
    · intro e he
      obtain ⟨r, her, hr⟩ := hc e he
      exact ⟨r, hr, her⟩
    · exact (simple_graph_rich_witness_graph_coloring_iff G _).mpr ⟨c, fun _ hr => hr⟩
  · rintro ⟨R, hR, hc⟩
    obtain ⟨c, hc⟩ := (simple_graph_rich_witness_graph_coloring_iff G R).mp hc
    refine ⟨c, ?_⟩
    intro e he
    obtain ⟨r, hr, her⟩ := hR e he
    exact ⟨r, her, hc r hr⟩
