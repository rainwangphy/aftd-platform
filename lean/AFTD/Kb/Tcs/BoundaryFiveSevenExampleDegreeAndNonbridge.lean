import AFTD.Prelude
import AFTD.Kb.Tcs.BoundaryFiveSevenExampleEdgeEssential

/-!
# boundary_five_seven_example_degree_and_nonbridge

Topic: graphs   Node: 5d6ca21285b0

Provenance: helper lemma. OP-1957: the size-(5,7) nonbridge obstruction; experiment 37140.

The explicitly defined 28-vertex graph has minimum degree at least 16, the displayed residual has a perfect matching, and its edge 0–14 has an alternate path after deletion.
-/

theorem boundary_five_seven_example_degree_and_nonbridge :
    (∀ v, 16 ≤ (in1122_fiveseven_graph.neighborFinset v).card) ∧
    (∃ P : (in1122_fiveseven_graph.induce {v | v ∈ in1122_fiveseven_residual}).Subgraph, P.IsPerfectMatching) ∧
    ((in1122_fiveseven_graph.induce {v | v ∈ in1122_fiveseven_residual}).deleteEdges
      {s(⟨0,by decide⟩,⟨14,by decide⟩)}).Reachable ⟨0,by decide⟩ ⟨14,by decide⟩ := by
  exact ⟨in1122_fiveseven_min_degree, in1122_fiveseven_residual_matching, in1122_fiveseven_nonbridge⟩
