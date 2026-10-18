import AFTD.Prelude
import AFTD.Kb.Tcs.LlyPositiveEdgeConnectivityThreshold
import AFTD.Kb.Tcs.FiveVertexTStar
import AFTD.Kb.Tcs.FiveVertexTStarAdjDecidable
import AFTD.Kb.Tcs.FiveVertexTStarDistEq
import AFTD.Kb.Tcs.FiveVertexTStarWassersteinLe
import AFTD.Kb.Tcs.FiveVertexTStarWassersteinGe
import AFTD.Kb.Tcs.FiveVertexTStarConnectedEdgeConnectivity
import AFTD.Kb.Tcs.LlyFiveVertexTStarCurvature
import AFTD.Kb.Tcs.FiveVertexMinDegreeTwoEdiamLeTwo
import AFTD.Kb.Tcs.FiveVertexMinDegreeTwoWassersteinLtOne
import AFTD.Kb.Tcs.LlyFiveVertexPosOfMinDegreeTwo
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.Tcs.GraphEdgeConnectivity
import AFTD.Kb.Tcs.GraphEdgeConnectivityLeMinDegree

/-!
# lly_positive_edge_connectivity_threshold_five

Topic: graphs   Node: 0e1076c2e307

Provenance: original. Related work: Partial result on OP-165 (arXiv:2610.10559, after Theorem 1.4); found by exact computation over all graphs on 5 vertices (curvatures via the paper's Theorem 2.2 and min-cost flow).

c(5) = 2: every connected graph on 5 vertices with edge-connectivity at least 2 has positive Lin–Lu–Yau curvature on every edge, while the path-like tree with a vertex of degree 3 (edges 01, 03, 04, 12) has κ' = 1 and κ_LLY(0,1) = −1/3. So c(5) < ⌈2·5/3 − 1⌉ = 3: the threshold of OP-165 fails at n = 5 for a non-degenerate reason.
-/

theorem lly_positive_edge_connectivity_threshold_five :
    lly_positive_edge_connectivity_threshold 5 = 2 := by
  unfold lly_positive_edge_connectivity_threshold
  set S : Set ℕ := {k : ℕ | ∀ (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj],
    G.Connected → k ≤ graph_edge_connectivity G →
      ∀ (x y : Fin 5), G.Adj x y → 0 < graph_lly_curvature G x y}
  have h2S : 2 ∈ S := by
    intro G inst hconn hk x y hxy
    have hcard : Fintype.card (Fin 5) = 5 := Fintype.card_fin 5
    have hmin : 2 ≤ G.minDegree := by
      have hle := graph_edge_connectivity_le_minDegree G
      omega
    exact lly_five_vertex_pos_of_min_degree_two G hcard hconn hmin x y hxy
  have hne : S.Nonempty := ⟨2, h2S⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem hne
  have hle2 : sInf S ≤ 2 := Nat.sInf_le h2S
  have hnot_le1 : ¬ (sInf S ≤ 1) := by
    intro hle1
    have hT_conn := five_vertex_t_star_connected_edge_connectivity.1
    have hT_ec := five_vertex_t_star_connected_edge_connectivity.2
    have hT_adj : five_vertex_t_star.Adj 0 1 := by decide
    have hcurv := hmem five_vertex_t_star hT_conn (by omega) 0 1 hT_adj
    have hval := lly_five_vertex_t_star_curvature
    linarith
  omega
