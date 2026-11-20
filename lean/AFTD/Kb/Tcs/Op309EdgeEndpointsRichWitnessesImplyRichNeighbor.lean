import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring

/-!
# op309_edge_endpoints_rich_witnesses_imply_rich_neighbor

Topic: graphs   Node: 73728e22b2a9

Provenance: helper lemma. Assembly step for triangle-dominated cubic graphs in OP-309.

If rich edges meet an endpoint of every edge, and each designated rich edge has a different adjacent designated rich edge, the coloring is rich-neighbor.
-/

theorem op309_edge_endpoints_rich_witnesses_imply_rich_neighbor
    {V : Type*} (G : SimpleGraph V) (c : G.lineGraph.Coloring (Fin 5))
    (R : Set G.edgeSet)
    (hrich : ∀ e ∈ R, simple_graph_edge_is_rich G c e)
    (hcover : ∀ e : G.edgeSet, ∃ v : V, v ∈ e.1 ∧ ∃ f ∈ R, v ∈ f.1)
    (hpaired : ∀ e ∈ R, ∃ f ∈ R, G.lineGraph.Adj e f) :
    simple_graph_is_rich_neighbor_coloring G c := by
  intro e _
  obtain ⟨v, hve, f, hfR, hvf⟩ := hcover e
  by_cases hef : e = f
  · subst hef
    obtain ⟨f', hf'R, hadj⟩ := hpaired e hfR
    exact ⟨f', hadj, hrich f' hf'R⟩
  · refine ⟨f, ?_, hrich f hfR⟩
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    exact ⟨hef, v, hve, hvf⟩
