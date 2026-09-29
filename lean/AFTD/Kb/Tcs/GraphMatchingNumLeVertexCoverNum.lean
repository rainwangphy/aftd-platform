import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMatchingNum
import AFTD.Kb.Tcs.GraphMatchingEncardLeVertexCoverEncard

/-!
# graph_matching_num_le_vertex_cover_num

Topic: graphs   Node: 701578ae21df

In any simple graph G, the matching number is at most the vertex cover number.
-/

/-- Weak duality: matching number is bounded above by vertex cover number. -/
theorem graph_matching_num_le_vertex_cover_num {V : Type*} (G : SimpleGraph V) : graph_matching_num G ≤ G.vertexCoverNum := by
  obtain ⟨s, hs1, hs2⟩ := G.vertexCoverNum_exists
  exact iSup_le fun M => iSup_le fun hM => hs1 ▸ graph_matching_encard_le_vertex_cover_encard G M s hM hs2
