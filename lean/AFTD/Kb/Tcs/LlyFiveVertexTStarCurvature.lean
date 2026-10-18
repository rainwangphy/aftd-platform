import AFTD.Prelude
import AFTD.Kb.Tcs.FiveVertexTStar
import AFTD.Kb.Tcs.FiveVertexTStarAdjDecidable
import AFTD.Kb.Tcs.FiveVertexTStarWassersteinLe
import AFTD.Kb.Tcs.FiveVertexTStarWassersteinGe
import AFTD.Kb.Tcs.GraphLlyCurvatureEqOfOllivierEq
import AFTD.Kb.Tcs.GraphOllivierCurvature
import AFTD.Kb.Tcs.FiveVertexTStarDistEq
import AFTD.Kb.Tcs.GraphWassersteinDist
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.Tcs.GraphIdleMeasure

/-!
# lly_five_vertex_t_star_curvature

Topic: graphs   Node: 8179682d3382

Provenance: helper lemma. step towards lly_positive_edge_connectivity_threshold_five

For the tree on 5 vertices with edges 0–1, 0–3, 0–4, 1–2 one has κ_LLY(0,1) = −1/3.
-/

/-- By the two Wasserstein bounds, κ_α(0,1) = 1 − W = (1−α)·(−1/3) for α ≥ 2/5, so the limit defining κ_LLY gives κ_LLY(0,1) = −1/3. This supplies the exact equality from the escalation, with the erroneous explicit plan replaced. -/
theorem lly_five_vertex_t_star_curvature :
    graph_lly_curvature five_vertex_t_star (0 : Fin 5) (1 : Fin 5) = -(1 / 3) := by
  have ha : (2 / 5 : ℝ) < 1 := by norm_num
  apply graph_lly_curvature_eq_of_ollivier_eq five_vertex_t_star 0 1 (-(1 / 3)) (2 / 5) ha
  intro α hα_lower hα_upper
  have hα0 : (2 / 5 : ℝ) ≤ α := le_of_lt hα_lower
  have hα1 : α ≤ 1 := le_of_lt hα_upper
  have h_le := five_vertex_t_star_wasserstein_le α hα0 hα1
  have hα0_ge : 0 ≤ α := by linarith
  have h_ge := five_vertex_t_star_wasserstein_ge α hα0_ge hα1
  have h_w : graph_wasserstein_dist five_vertex_t_star
      (graph_idle_measure five_vertex_t_star α 0) (graph_idle_measure five_vertex_t_star α 1) =
      4 / 3 - α / 3 := le_antisymm h_le h_ge
  unfold graph_ollivier_curvature
  rw [h_w]
  have h_dist : five_vertex_t_star.dist 0 1 = 1 := five_vertex_t_star_dist_eq.1
  rw [h_dist]
  push_cast
  ring
