import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMatchingNum
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.IsMatchingVertsEncardLeTwoMul
import AFTD.Kb.Tcs.ExistsIsMatchingIsVertexCover

/-!
# vertex_cover_num_le_two_mul_matching_num

Topic: approximation   Node: d88580866f59

Provenance: formalization of a published result. Source: Vazirani (2001), Approximation Algorithms, Theorem 1.1

In any finite simple graph G, the vertex cover number is at most twice the matching number: G.vertexCoverNum ≤ 2 * graph_matching_num G.
-/

/-- The vertex cover number is at most twice the matching number in any finite simple graph. -/
theorem vertex_cover_num_le_two_mul_matching_num {V : Type*} [Finite V] (G : SimpleGraph V) :
    G.vertexCoverNum ≤ 2 * graph_matching_num G := by
  obtain ⟨M, hM, hcov⟩ := exists_isMatching_isVertexCover G
  have h1 : G.vertexCoverNum ≤ M.verts.encard := by
    unfold SimpleGraph.vertexCoverNum
    exact iInf_le_of_le M.verts (iInf_le (fun (_ : G.IsVertexCover M.verts) => M.verts.encard) hcov)
  have h2 : M.verts.encard ≤ 2 * M.edgeSet.encard :=
    isMatching_verts_encard_le_two_mul M hM
  have h3 : M.edgeSet.encard ≤ graph_matching_num G := by
    unfold graph_matching_num
    exact le_iSup_of_le M (le_iSup (fun (_ : M.IsMatching) => M.edgeSet.encard) hM)
  have h4 : 2 * M.edgeSet.encard ≤ 2 * graph_matching_num G :=
    mul_le_mul_right h3 2
  exact h1.trans (h2.trans h4)
