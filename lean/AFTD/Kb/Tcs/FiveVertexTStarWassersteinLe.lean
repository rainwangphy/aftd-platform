import AFTD.Prelude
import AFTD.Kb.Tcs.FiveVertexTStar
import AFTD.Kb.Tcs.FiveVertexTStarAdjDecidable
import AFTD.Kb.Tcs.FiveVertexTStarDistEq
import AFTD.Kb.Tcs.GraphWassersteinDistLeOfPlan
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphWassersteinDist

/-!
# five_vertex_t_star_wasserstein_le

Topic: graphs   Node: 20ba1b386711

Provenance: helper lemma. step towards lly_positive_edge_connectivity_threshold_five

For the T-graph and α in [2/5, 1], the explicit plan π(0,0)=(1−α)/2, π(0,1)=(5α−2)/3, π(0,2)=(1−α)/6, π(1,2)=(1−α)/3, π(3,1)=(1−α)/3, π(4,1)=(1−α)/3 shows W(μ_0^α, μ_1^α) ≤ 4/3 − α/3.
-/

/-- Upper bound for the T-graph by an explicit transport plan. NOTE: the plan proposed in the earlier escalation was infeasible (its column-1 sum is (4α−1)/3, not α). The corrected table is: π(0,0)=(1−α)/2, π(0,1)=(5α−2)/3, π(0,2)=(1−α)/6, π(1,2)=(1−α)/3, π(3,1)=(1−α)/3, π(4,1)=(1−α)/3, everything else 0; it needs α ≥ 2/5 and has cost exactly 4/3 − α/3. -/
theorem five_vertex_t_star_wasserstein_le (α : ℝ) (hα0 : 2 / 5 ≤ α) (hα1 : α ≤ 1) :
    graph_wasserstein_dist five_vertex_t_star (graph_idle_measure five_vertex_t_star α 0)
      (graph_idle_measure five_vertex_t_star α 1) ≤ 4 / 3 - α / 3 := by
  let π : Fin 5 → Fin 5 → ℝ := fun a b =>
    if a = 0 ∧ b = 0 then (1 - α) / 2
    else if a = 0 ∧ b = 1 then (5 * α - 2) / 3
    else if a = 0 ∧ b = 2 then (1 - α) / 6
    else if a = 1 ∧ b = 2 then (1 - α) / 3
    else if a = 3 ∧ b = 1 then (1 - α) / 3
    else if a = 4 ∧ b = 1 then (1 - α) / 3
    else 0
  have hπ : ∀ a b, 0 ≤ π a b := by
    intro a b
    fin_cases a <;> fin_cases b <;> { dsimp [π]; linarith }
  have h1 : ∀ a, ∑ b, π a b = graph_idle_measure five_vertex_t_star α 0 a := by
    intro a
    fin_cases a
    · rw [Fin.sum_univ_five]; dsimp [π]
      have : graph_idle_measure five_vertex_t_star α 0 0 = α := by
        unfold graph_idle_measure; simp
      rw [this]; ring
    · rw [Fin.sum_univ_five]; dsimp [π]
      have : graph_idle_measure five_vertex_t_star α 0 1 = (1 - α) / 3 := by
        unfold graph_idle_measure
        rw [if_neg (by decide), if_pos (by decide)]
        have hd : five_vertex_t_star.degree 0 = 3 := by decide
        rw [hd]; norm_cast
      rw [this]; ring
    · rw [Fin.sum_univ_five]; dsimp [π]
      have : graph_idle_measure five_vertex_t_star α 0 2 = 0 := by
        unfold graph_idle_measure
        rw [if_neg (by decide), if_neg (by decide)]
      rw [this]; ring
    · rw [Fin.sum_univ_five]; dsimp [π]
      have : graph_idle_measure five_vertex_t_star α 0 3 = (1 - α) / 3 := by
        unfold graph_idle_measure
        rw [if_neg (by decide), if_pos (by decide)]
        have hd : five_vertex_t_star.degree 0 = 3 := by decide
        rw [hd]; norm_cast
      rw [this]; ring
    · rw [Fin.sum_univ_five]; dsimp [π]
      have : graph_idle_measure five_vertex_t_star α 0 4 = (1 - α) / 3 := by
        unfold graph_idle_measure
        rw [if_neg (by decide), if_pos (by decide)]
        have hd : five_vertex_t_star.degree 0 = 3 := by decide
        rw [hd]; norm_cast
      rw [this]; ring
  have h2 : ∀ b, ∑ a, π a b = graph_idle_measure five_vertex_t_star α 1 b := by
    intro b
    fin_cases b
    · rw [Fin.sum_univ_five]; dsimp [π]
      have : graph_idle_measure five_vertex_t_star α 1 0 = (1 - α) / 2 := by
        unfold graph_idle_measure
        rw [if_neg (by decide), if_pos (by decide)]
        have hd : five_vertex_t_star.degree 1 = 2 := by decide
        rw [hd]; norm_cast
      rw [this]; ring
    · rw [Fin.sum_univ_five]; dsimp [π]
      have : graph_idle_measure five_vertex_t_star α 1 1 = α := by
        unfold graph_idle_measure; simp
      rw [this]; ring
    · rw [Fin.sum_univ_five]; dsimp [π]
      have : graph_idle_measure five_vertex_t_star α 1 2 = (1 - α) / 2 := by
        unfold graph_idle_measure
        rw [if_neg (by decide), if_pos (by decide)]
        have hd : five_vertex_t_star.degree 1 = 2 := by decide
        rw [hd]; norm_cast
      rw [this]; ring
    · rw [Fin.sum_univ_five]; dsimp [π]
      have : graph_idle_measure five_vertex_t_star α 1 3 = 0 := by
        unfold graph_idle_measure
        rw [if_neg (by decide), if_neg (by decide)]
      rw [this]; ring
    · rw [Fin.sum_univ_five]; dsimp [π]
      have : graph_idle_measure five_vertex_t_star α 1 4 = 0 := by
        unfold graph_idle_measure
        rw [if_neg (by decide), if_neg (by decide)]
      rw [this]; ring
  have hcost : (∑ a, ∑ b, (five_vertex_t_star.dist a b : ℝ) * π a b) = 4 / 3 - α / 3 := by
    have hd00 : five_vertex_t_star.dist 0 0 = 0 := SimpleGraph.dist_self
    have hd01 : five_vertex_t_star.dist 0 1 = 1 := five_vertex_t_star_dist_eq.1
    have hd02 : five_vertex_t_star.dist 0 2 = 2 := five_vertex_t_star_dist_eq.2.1
    have hd12 : five_vertex_t_star.dist 1 2 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr (by decide)
    have hd31 : five_vertex_t_star.dist 3 1 = 2 := five_vertex_t_star_dist_eq.2.2.1
    have hd41 : five_vertex_t_star.dist 4 1 = 2 := five_vertex_t_star_dist_eq.2.2.2.1
    repeat rw [Fin.sum_univ_five]
    dsimp [π]
    rw [hd00, hd01, hd02, hd12, hd31, hd41]
    push_cast
    ring
  have h_bound := graph_wasserstein_dist_le_of_plan five_vertex_t_star
    (graph_idle_measure five_vertex_t_star α 0) (graph_idle_measure five_vertex_t_star α 1) π hπ h1 h2
  rw [hcost] at h_bound
  exact h_bound
