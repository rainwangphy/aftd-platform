import AFTD.Prelude
import AFTD.Kb.Tcs.FiveVertexMinDegreeTwoEdiamLeTwo
import AFTD.Kb.Tcs.GraphWassersteinDistLeOfPlan
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphIdleMeasureSumEqOne
import AFTD.Kb.Tcs.GraphIdleMeasureNonneg
import AFTD.Kb.Tcs.WassersteinDistLeOfDiameterTwo
import AFTD.Kb.Tcs.FiveVertexMinDegreeTwoIdleCouplingBound
import AFTD.Kb.Tcs.GraphWassersteinDist

/-!
# five_vertex_min_degree_two_wasserstein_lt_one

Topic: graphs   Node: b71a4cce7f2f

Provenance: helper lemma. step towards lly_positive_edge_connectivity_threshold_five

Every connected graph on 5 vertices with minimum degree at least 2 has, for each edge xy, some α ∈ (0, 1) with W(μ_x^α, μ_y^α) < 1.
-/

/-- The geometric core of part (i): on 5 vertices with δ ≥ 2, every edge admits some α ∈ (0,1) where the two lazy measures are closer than 1 in W. Uses δ ≥ 2 = (n−1)/2 hence ediam ≤ 2, so all non-neighbour pairs are at distance exactly 2. -/
theorem five_vertex_min_degree_two_wasserstein_lt_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 5) (hG : G.Connected)
    (hδ : 2 ≤ G.minDegree) (x y : V) (hxy : G.Adj x y) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y) < 1 := by
  have _ := hG
  use 1 / 2
  refine ⟨by norm_num, by norm_num, ?_⟩
  have hdeg_x : 0 < G.degree x := by
    have := G.minDegree_le_degree x
    omega
  have hdeg_y : 0 < G.degree y := by
    have := G.minDegree_le_degree y
    omega
  have hμ_nonneg : ∀ a, 0 ≤ graph_idle_measure G (1 / 2) x a := by
    intro a
    exact graph_idle_measure_nonneg G (1 / 2) (by norm_num) (by norm_num) x a
  have hν_nonneg : ∀ b, 0 ≤ graph_idle_measure G (1 / 2) y b := by
    intro b
    exact graph_idle_measure_nonneg G (1 / 2) (by norm_num) (by norm_num) y b
  have hμ_sum : ∑ a, graph_idle_measure G (1 / 2) x a = 1 :=
    graph_idle_measure_sum_eq_one G (1 / 2) x hdeg_x
  have hν_sum : ∑ b, graph_idle_measure G (1 / 2) y b = 1 :=
    graph_idle_measure_sum_eq_one G (1 / 2) y hdeg_y
  have hediam : G.ediam ≤ 2 := five_vertex_min_degree_two_ediam_le_two G hcard hδ
  have hdist2 : ∀ a b : V, (G.dist a b : ℝ) ≤ 2 := by
    intro a b
    have hle : G.edist a b ≤ 2 := le_trans SimpleGraph.edist_le_ediam hediam
    have hnat : G.dist a b ≤ 2 := ENat.toNat_le_of_le_natCast hle
    exact Nat.cast_le.mpr hnat
  have hxy_dist : (G.dist x y : ℝ) = 1 := by
    rw [G.dist_eq_one_iff_adj.mpr hxy]
    norm_num
  have h_bound := wasserstein_dist_le_of_diameter_two G hdist2
    (graph_idle_measure G (1 / 2) x) (graph_idle_measure G (1 / 2) y)
    hμ_nonneg hν_nonneg hμ_sum hν_sum x y hxy_dist
  have h_comb := five_vertex_min_degree_two_idle_coupling_bound G hcard hδ x y hxy
  linarith
