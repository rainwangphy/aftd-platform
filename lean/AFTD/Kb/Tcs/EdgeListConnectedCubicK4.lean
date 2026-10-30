import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeListConnectedCubic

/-!
# edge_list_connected_cubic_k4

Topic: np_completeness   Node: f295f65750d2

Provenance: helper lemma. Sanity check of edge_list_connected_cubic (K4 is a connected cubic graph), for arXiv:2610.35794 (Computational complexity of the H-coloring problem in cubic graphs)

The edge list [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)] of the complete graph K4 on the vertices 0..3 satisfies edge_list_connected_cubic 4.
-/

theorem edge_list_connected_cubic_k4 :
    edge_list_connected_cubic 4 [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)] := by
  refine ⟨by decide, by decide, by decide⟩
