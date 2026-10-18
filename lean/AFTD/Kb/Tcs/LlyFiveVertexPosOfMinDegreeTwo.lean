import AFTD.Prelude
import AFTD.Kb.Tcs.FiveVertexMinDegreeTwoWassersteinLtOne
import AFTD.Kb.Tcs.GraphLlyCurvaturePosOfWassersteinLtOne
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphWassersteinDist
import AFTD.Kb.Tcs.GraphLlyCurvature

/-!
# lly_five_vertex_pos_of_min_degree_two

Topic: graphs   Node: 019b579946d3

Provenance: helper lemma. step towards lly_positive_edge_connectivity_threshold_five

Every connected graph on 5 vertices with minimum degree at least 2 has positive Lin–Lu–Yau curvature on every edge.
-/

/-- Every connected graph on 5 vertices with minimum degree at least 2 has positive Lin–Lu–Yau curvature on every edge: apply the Wasserstein < 1 criterion at the α produced by the diameter-2 plan argument. This is the `2 ∈ S` half of the parent. -/
theorem lly_five_vertex_pos_of_min_degree_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 5) (hG : G.Connected)
    (hδ : 2 ≤ G.minDegree) (x y : V) (hxy : G.Adj x y) : 0 < graph_lly_curvature G x y := by
  obtain ⟨α, hα0, hα1, hW⟩ := five_vertex_min_degree_two_wasserstein_lt_one G hcard hG hδ x y hxy
  exact graph_lly_curvature_pos_of_wasserstein_lt_one G hG x y hxy α hα0 hα1 hW
