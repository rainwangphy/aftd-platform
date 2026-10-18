import AFTD.Prelude
import AFTD.Kb.Tcs.FiveVertexTStar
import AFTD.Kb.Tcs.FiveVertexTStarAdjDecidable
import AFTD.Kb.Tcs.FiveVertexTStarDistEq
import AFTD.Kb.Tcs.GraphWassersteinDistGeOfLipschitz
import AFTD.Kb.Tcs.GraphIdleMeasureSumEqOne
import AFTD.Kb.Tcs.GraphIdleMeasureNonneg
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphWassersteinDist

/-!
# five_vertex_t_star_wasserstein_ge

Topic: graphs   Node: db57f26eaada

Provenance: helper lemma. step towards lly_positive_edge_connectivity_threshold_five

For the T-graph and α in [0,1], 4/3 − α/3 ≤ W(μ_0^α, μ_1^α), because f(v) = d(v,2) is 1-Lipschitz and Σ f μ_0^α − Σ f μ_1^α = (2α + 7(1−α)/3) − 1 = 4/3 − α/3.
-/

/-- Lower bound for the T-graph by Kantorovich duality with the 1-Lipschitz test function f = dist(·,2), whose values on the vertices are (2,1,0,3,3). -/
theorem five_vertex_t_star_wasserstein_ge (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    4 / 3 - α / 3 ≤ graph_wasserstein_dist five_vertex_t_star
      (graph_idle_measure five_vertex_t_star α 0) (graph_idle_measure five_vertex_t_star α 1) := by
  have hconn : five_vertex_t_star.Connected := by decide
  let f : Fin 5 → ℝ := fun v => (five_vertex_t_star.dist v 2 : ℝ)
  have hf : ∀ a b, f a - f b ≤ (five_vertex_t_star.dist a b : ℝ) := by
    intro a b
    dsimp [f]
    have := hconn.dist_triangle (u := a) (v := b) (w := 2)
    have h : (five_vertex_t_star.dist a 2 : ℝ) ≤ (five_vertex_t_star.dist a b : ℝ) + (five_vertex_t_star.dist b 2 : ℝ) := by
      exact_mod_cast this
    linarith
  have hμ_nonneg : ∀ a, 0 ≤ graph_idle_measure five_vertex_t_star α 0 a := by
    intro a
    exact graph_idle_measure_nonneg five_vertex_t_star α hα0 hα1 0 a
  have hν_nonneg : ∀ b, 0 ≤ graph_idle_measure five_vertex_t_star α 1 b := by
    intro b
    exact graph_idle_measure_nonneg five_vertex_t_star α hα0 hα1 1 b
  have hd0 : 0 < five_vertex_t_star.degree 0 := by decide
  have hd1 : 0 < five_vertex_t_star.degree 1 := by decide
  have hμ1 : ∑ a, graph_idle_measure five_vertex_t_star α 0 a = 1 :=
    graph_idle_measure_sum_eq_one five_vertex_t_star α 0 hd0
  have hν1 : ∑ b, graph_idle_measure five_vertex_t_star α 1 b = 1 :=
    graph_idle_measure_sum_eq_one five_vertex_t_star α 1 hd1
  have hge := graph_wasserstein_dist_ge_of_lipschitz five_vertex_t_star
    (graph_idle_measure five_vertex_t_star α 0) (graph_idle_measure five_vertex_t_star α 1)
    hμ_nonneg hν_nonneg hμ1 hν1 f hf

  have hd00 : five_vertex_t_star.dist 0 2 = 2 := five_vertex_t_star_dist_eq.2.1
  have hd12 : five_vertex_t_star.dist 1 2 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr (by decide)
  have hd22 : five_vertex_t_star.dist 2 2 = 0 := SimpleGraph.dist_self
  have hd32 : five_vertex_t_star.dist 3 2 = 3 := five_vertex_t_star_dist_eq.2.2.2.2.1
  have hd42 : five_vertex_t_star.dist 4 2 = 3 := five_vertex_t_star_dist_eq.2.2.2.2.2

  have hμ0 : graph_idle_measure five_vertex_t_star α 0 0 = α := by
    unfold graph_idle_measure; simp
  have hμ1_val : graph_idle_measure five_vertex_t_star α 0 1 = (1 - α) / 3 := by
    unfold graph_idle_measure
    rw [if_neg (by decide), if_pos (by decide)]
    have hd : five_vertex_t_star.degree 0 = 3 := by decide
    rw [hd]; norm_cast
  have hμ2_val : graph_idle_measure five_vertex_t_star α 0 2 = 0 := by
    unfold graph_idle_measure
    rw [if_neg (by decide), if_neg (by decide)]
  have hμ3_val : graph_idle_measure five_vertex_t_star α 0 3 = (1 - α) / 3 := by
    unfold graph_idle_measure
    rw [if_neg (by decide), if_pos (by decide)]
    have hd : five_vertex_t_star.degree 0 = 3 := by decide
    rw [hd]; norm_cast
  have hμ4_val : graph_idle_measure five_vertex_t_star α 0 4 = (1 - α) / 3 := by
    unfold graph_idle_measure
    rw [if_neg (by decide), if_pos (by decide)]
    have hd : five_vertex_t_star.degree 0 = 3 := by decide
    rw [hd]; norm_cast

  have hν0_val : graph_idle_measure five_vertex_t_star α 1 0 = (1 - α) / 2 := by
    unfold graph_idle_measure
    rw [if_neg (by decide), if_pos (by decide)]
    have hd : five_vertex_t_star.degree 1 = 2 := by decide
    rw [hd]; norm_cast
  have hν1_val : graph_idle_measure five_vertex_t_star α 1 1 = α := by
    unfold graph_idle_measure; simp
  have hν2_val : graph_idle_measure five_vertex_t_star α 1 2 = (1 - α) / 2 := by
    unfold graph_idle_measure
    rw [if_neg (by decide), if_pos (by decide)]
    have hd : five_vertex_t_star.degree 1 = 2 := by decide
    rw [hd]; norm_cast
  have hν3_val : graph_idle_measure five_vertex_t_star α 1 3 = 0 := by
    unfold graph_idle_measure
    rw [if_neg (by decide), if_neg (by decide)]
  have hν4_val : graph_idle_measure five_vertex_t_star α 1 4 = 0 := by
    unfold graph_idle_measure
    rw [if_neg (by decide), if_neg (by decide)]

  have hdiff : ∑ a, f a * graph_idle_measure five_vertex_t_star α 0 a -
      ∑ b, f b * graph_idle_measure five_vertex_t_star α 1 b = 4 / 3 - α / 3 := by
    rw [Fin.sum_univ_five, Fin.sum_univ_five]
    dsimp [f]
    rw [hd00, hd12, hd22, hd32, hd42]
    rw [hμ0, hμ1_val, hμ2_val, hμ3_val, hμ4_val]
    rw [hν0_val, hν1_val, hν2_val, hν3_val, hν4_val]
    push_cast
    ring

  linarith
