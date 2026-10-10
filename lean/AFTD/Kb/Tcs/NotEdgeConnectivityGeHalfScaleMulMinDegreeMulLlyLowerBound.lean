import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvatureLowerBound
import AFTD.Kb.Tcs.GraphEdgeConnectivity
import AFTD.Kb.Tcs.GraphLlyCurvatureEqOfOllivierEq
import AFTD.Kb.Tcs.GraphWassersteinDistLeOfPlan
import AFTD.Kb.Tcs.GraphWassersteinDistGeOfLipschitz
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.GraphOllivierCurvature
import AFTD.Kb.Tcs.GraphIdleMeasureNonneg
import AFTD.Kb.Tcs.GraphIdleMeasureSumEqOne
import AFTD.Kb.Tcs.GraphWassersteinDist
import AFTD.Kb.Tcs.GraphLlyCurvatureComm
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# not_edge_connectivity_ge_half_scale_mul_min_degree_mul_lly_lower_bound

Topic: graphs   Node: 14cb567cef9a

Provenance: original. Related work: Answers OP-164 (asked after arXiv:2610.10559, Theorem 1.2, which is the case d = 3) in the negative. Found by exact computation (curvatures by min-cost flow at idleness 0.9, 0.99, 0.999, all giving 3/8); no connected graph on at most 6 vertices is a counterexample. Theorem 1.2 itself holds on this graph: κ_LLY^(3) = 1/6.

The inequality κ'(G) ≥ (d/2) δ(G) κ_LLY^(d)(G) asked in OP-164 fails for d = 4: take a 4-cycle 0–1–2–3–0 and a triangle 4–5–6 joined by the bridge 2–4 (7 vertices). It is connected with diameter 4, δ = 2 and κ' = 1, and the only pairs at distance 4, {0, 5} and {0, 6}, have κ_LLY = 3/8, so (4/2)·2·(3/8) = 3/2 > 1.
-/

/-- The edge list of a 4-cycle 0-1-2-3 and a triangle 4-5-6 joined by the bridge 2-4. -/
def c4_bridge_k3_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,4),(2,4)]

def c4_bridge_k3_graph : SimpleGraph (Fin 7) where
  Adj i j := (i.val, j.val) ∈ c4_bridge_k3_edges ∨ (j.val, i.val) ∈ c4_bridge_k3_edges
  symm := ⟨fun _ _ (h : _ ∨ _) => h.symm⟩
  loopless := ⟨by decide⟩

instance c4_bridge_k3_graph_decAdj : DecidableRel c4_bridge_k3_graph.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ c4_bridge_k3_edges ∨ (j.val, i.val) ∈ c4_bridge_k3_edges))

theorem walk_sub_le_length_of_adj_sub_le_one {V : Type*} {G : SimpleGraph V} (f : V → ℤ)
    (hf : ∀ u v, G.Adj u v → f u - f v ≤ 1) :
    ∀ {a b : V} (p : G.Walk a b), f a - f b ≤ p.length
  | _, _, .nil => by simp
  | _, _, .cons h p => by
      have h1 := walk_sub_le_length_of_adj_sub_le_one f hf p
      have h2 := hf _ _ h
      rw [SimpleGraph.Walk.length_cons]
      push_cast
      linarith

theorem sub_le_dist_of_adj_sub_le_one {V : Type*} {G : SimpleGraph V} (f : V → ℤ)
    (hf : ∀ u v, G.Adj u v → f u - f v ≤ 1) {a b : V} (h : G.Reachable a b) :
    f a - f b ≤ G.dist a b := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  rw [← hp]
  exact walk_sub_le_length_of_adj_sub_le_one f hf p

theorem c4_bridge_k3_graph_connected : c4_bridge_k3_graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨2, fun w => ?_⟩
  have r : ∀ a b, c4_bridge_k3_graph.Adj a b → c4_bridge_k3_graph.Reachable a b :=
    fun a b h => h.reachable
  fin_cases w
  · exact (r 2 1 (by decide)).trans (r 1 0 (by decide))
  · exact r 2 1 (by decide)
  · exact SimpleGraph.Reachable.refl _
  · exact r 2 3 (by decide)
  · exact r 2 4 (by decide)
  · exact (r 2 4 (by decide)).trans (r 4 5 (by decide))
  · exact (r 2 4 (by decide)).trans (r 4 6 (by decide))

/-- Distance from vertex 0. -/
def c4_bridge_k3_label : Fin 7 → ℤ := ![0, 1, 2, 1, 3, 4, 4]

theorem c4_bridge_k3_label_lip :
    ∀ u v, c4_bridge_k3_graph.Adj u v → c4_bridge_k3_label u - c4_bridge_k3_label v ≤ 1 := by
  decide

theorem c4_bridge_k3_dist_ge (a b : Fin 7) :
    ((c4_bridge_k3_label a : ℝ) - c4_bridge_k3_label b) ≤ c4_bridge_k3_graph.dist a b := by
  have := sub_le_dist_of_adj_sub_le_one c4_bridge_k3_label c4_bridge_k3_label_lip
    (c4_bridge_k3_graph_connected.preconnected a b)
  exact_mod_cast this

theorem c4_bridge_k3_dist_le_of_adj (a b : Fin 7) (h : c4_bridge_k3_graph.Adj a b) :
    c4_bridge_k3_graph.dist a b ≤ 1 :=
  (SimpleGraph.dist_eq_one_iff_adj.mpr h).le

theorem c4_bridge_k3_dist_zero_five : c4_bridge_k3_graph.dist 0 5 = 4 := by
  apply le_antisymm
  · have t1 := c4_bridge_k3_graph_connected.dist_triangle (u := 0) (v := 3) (w := 5)
    have t2 := c4_bridge_k3_graph_connected.dist_triangle (u := 3) (v := 2) (w := 5)
    have t3 := c4_bridge_k3_graph_connected.dist_triangle (u := 2) (v := 4) (w := 5)
    have := c4_bridge_k3_dist_le_of_adj 0 3 (by decide)
    have := c4_bridge_k3_dist_le_of_adj 3 2 (by decide)
    have := c4_bridge_k3_dist_le_of_adj 2 4 (by decide)
    have := c4_bridge_k3_dist_le_of_adj 4 5 (by decide)
    omega
  · have := sub_le_dist_of_adj_sub_le_one c4_bridge_k3_label c4_bridge_k3_label_lip
      (c4_bridge_k3_graph_connected.preconnected 5 0)
    have e : c4_bridge_k3_label 5 - c4_bridge_k3_label 0 = 4 := by decide
    rw [SimpleGraph.dist_comm] at this
    omega

theorem c4_bridge_k3_dist_zero_six : c4_bridge_k3_graph.dist 0 6 = 4 := by
  apply le_antisymm
  · have t1 := c4_bridge_k3_graph_connected.dist_triangle (u := 0) (v := 3) (w := 6)
    have t2 := c4_bridge_k3_graph_connected.dist_triangle (u := 3) (v := 2) (w := 6)
    have t3 := c4_bridge_k3_graph_connected.dist_triangle (u := 2) (v := 4) (w := 6)
    have := c4_bridge_k3_dist_le_of_adj 0 3 (by decide)
    have := c4_bridge_k3_dist_le_of_adj 3 2 (by decide)
    have := c4_bridge_k3_dist_le_of_adj 2 4 (by decide)
    have := c4_bridge_k3_dist_le_of_adj 4 6 (by decide)
    omega
  · have := sub_le_dist_of_adj_sub_le_one c4_bridge_k3_label c4_bridge_k3_label_lip
      (c4_bridge_k3_graph_connected.preconnected 6 0)
    have e : c4_bridge_k3_label 6 - c4_bridge_k3_label 0 = 4 := by decide
    rw [SimpleGraph.dist_comm] at this
    omega

theorem c4_bridge_k3_dist_le_two_three (a c b : Fin 7) (h1 : c4_bridge_k3_graph.Adj a c)
    (h2 : c4_bridge_k3_graph.Adj c b) : c4_bridge_k3_graph.dist a b ≤ 2 := by
  have t := c4_bridge_k3_graph_connected.dist_triangle (u := a) (v := c) (w := b)
  have := c4_bridge_k3_dist_le_of_adj a c h1
  have := c4_bridge_k3_dist_le_of_adj c b h2
  omega

theorem c4_bridge_k3_lly_zero_five :
    graph_lly_curvature c4_bridge_k3_graph 0 5 = 3 / 8 := by
  apply graph_lly_curvature_eq_of_ollivier_eq c4_bridge_k3_graph 0 5 (3 / 8) 0 (by norm_num)
  intro α hα0 hα1
  have hdeg0 : c4_bridge_k3_graph.degree 0 = 2 := by decide
  have hdeg5 : c4_bridge_k3_graph.degree 5 = 2 := by decide
  have hd14 : c4_bridge_k3_graph.dist 1 4 ≤ 2 := c4_bridge_k3_dist_le_two_three 1 2 4 (by decide) (by decide)
  have hd36 : c4_bridge_k3_graph.dist 3 6 ≤ 3 := by
    have t := c4_bridge_k3_graph_connected.dist_triangle (u := 3) (v := 2) (w := 6)
    have := c4_bridge_k3_dist_le_of_adj 3 2 (by decide)
    have := c4_bridge_k3_dist_le_two_three 2 4 6 (by decide) (by decide)
    omega
  have hW : graph_wasserstein_dist c4_bridge_k3_graph (graph_idle_measure c4_bridge_k3_graph α 0)
      (graph_idle_measure c4_bridge_k3_graph α 5) = 4 * α + 5 / 2 * (1 - α) := by
    apply le_antisymm
    · let π : Fin 7 → Fin 7 → ℝ := fun a b =>
        if a = 0 ∧ b = 5 then α else if a = 1 ∧ b = 4 then (1 - α) / 2
        else if a = 3 ∧ b = 6 then (1 - α) / 2 else 0
      have h0 : ∀ a b, 0 ≤ π a b := by
        intro a b; simp only [π]; split_ifs <;> linarith
      refine (graph_wasserstein_dist_le_of_plan _ _ _ π h0 ?_ ?_).trans ?_
      · intro a
        fin_cases a <;> simp +decide [π, Fin.sum_univ_seven, graph_idle_measure, hdeg0]
      · intro b
        fin_cases b <;> simp +decide [π, Fin.sum_univ_seven, graph_idle_measure, hdeg5]
      · have e : ∑ a, ∑ b, (c4_bridge_k3_graph.dist a b : ℝ) * π a b =
            (c4_bridge_k3_graph.dist 0 5 : ℝ) * α + (c4_bridge_k3_graph.dist 1 4 : ℝ) * ((1 - α) / 2)
              + (c4_bridge_k3_graph.dist 3 6 : ℝ) * ((1 - α) / 2) := by
          simp [π, Fin.sum_univ_seven]
        rw [e, c4_bridge_k3_dist_zero_five]
        have c0 : (0 : ℝ) ≤ (1 - α) / 2 := by linarith
        have e1 : (c4_bridge_k3_graph.dist 1 4 : ℝ) ≤ 2 := by exact_mod_cast hd14
        have e2 : (c4_bridge_k3_graph.dist 3 6 : ℝ) ≤ 3 := by exact_mod_cast hd36
        nlinarith [mul_le_mul_of_nonneg_right e1 c0, mul_le_mul_of_nonneg_right e2 c0]
    · have hs0 := graph_idle_measure_sum_eq_one c4_bridge_k3_graph α 0 (by rw [hdeg0]; norm_num)
      have hs5 := graph_idle_measure_sum_eq_one c4_bridge_k3_graph α 5 (by rw [hdeg5]; norm_num)
      have hf : ∀ a b, (fun v => -(c4_bridge_k3_label v : ℝ)) a -
          (fun v => -(c4_bridge_k3_label v : ℝ)) b ≤ (c4_bridge_k3_graph.dist a b : ℝ) := by
        intro a b
        have := c4_bridge_k3_dist_ge b a
        rw [SimpleGraph.dist_comm] at this
        simp only
        linarith
      have := graph_wasserstein_dist_ge_of_lipschitz c4_bridge_k3_graph _ _
        (graph_idle_measure_nonneg c4_bridge_k3_graph α hα0.le hα1.le 0)
        (graph_idle_measure_nonneg c4_bridge_k3_graph α hα0.le hα1.le 5) hs0 hs5 _ hf
      have e0 : ∑ a, (fun v => -(c4_bridge_k3_label v : ℝ)) a *
          graph_idle_measure c4_bridge_k3_graph α 0 a = -(1 - α) := by
        simp +decide [Fin.sum_univ_seven, graph_idle_measure, hdeg0, c4_bridge_k3_label]
        ring
      have e5 : ∑ a, (fun v => -(c4_bridge_k3_label v : ℝ)) a *
          graph_idle_measure c4_bridge_k3_graph α 5 a = -(4 * α + 7 / 2 * (1 - α)) := by
        simp +decide [Fin.sum_univ_seven, graph_idle_measure, hdeg5, c4_bridge_k3_label]
        ring
      rw [e0, e5] at this
      linarith
  unfold graph_ollivier_curvature
  rw [hW, c4_bridge_k3_dist_zero_five]
  push_cast
  ring

theorem c4_bridge_k3_lly_zero_six :
    graph_lly_curvature c4_bridge_k3_graph 0 6 = 3 / 8 := by
  apply graph_lly_curvature_eq_of_ollivier_eq c4_bridge_k3_graph 0 6 (3 / 8) 0 (by norm_num)
  intro α hα0 hα1
  have hdeg0 : c4_bridge_k3_graph.degree 0 = 2 := by decide
  have hdeg6 : c4_bridge_k3_graph.degree 6 = 2 := by decide
  have hd14 : c4_bridge_k3_graph.dist 1 4 ≤ 2 := c4_bridge_k3_dist_le_two_three 1 2 4 (by decide) (by decide)
  have hd35 : c4_bridge_k3_graph.dist 3 5 ≤ 3 := by
    have t := c4_bridge_k3_graph_connected.dist_triangle (u := 3) (v := 2) (w := 5)
    have := c4_bridge_k3_dist_le_of_adj 3 2 (by decide)
    have := c4_bridge_k3_dist_le_two_three 2 4 5 (by decide) (by decide)
    omega
  have hW : graph_wasserstein_dist c4_bridge_k3_graph (graph_idle_measure c4_bridge_k3_graph α 0)
      (graph_idle_measure c4_bridge_k3_graph α 6) = 4 * α + 5 / 2 * (1 - α) := by
    apply le_antisymm
    · let π : Fin 7 → Fin 7 → ℝ := fun a b =>
        if a = 0 ∧ b = 6 then α else if a = 1 ∧ b = 4 then (1 - α) / 2
        else if a = 3 ∧ b = 5 then (1 - α) / 2 else 0
      have h0 : ∀ a b, 0 ≤ π a b := by
        intro a b; simp only [π]; split_ifs <;> linarith
      refine (graph_wasserstein_dist_le_of_plan _ _ _ π h0 ?_ ?_).trans ?_
      · intro a
        fin_cases a <;> simp +decide [π, Fin.sum_univ_seven, graph_idle_measure, hdeg0]
      · intro b
        fin_cases b <;> simp +decide [π, Fin.sum_univ_seven, graph_idle_measure, hdeg6]
      · have e : ∑ a, ∑ b, (c4_bridge_k3_graph.dist a b : ℝ) * π a b =
            (c4_bridge_k3_graph.dist 0 6 : ℝ) * α + (c4_bridge_k3_graph.dist 1 4 : ℝ) * ((1 - α) / 2)
              + (c4_bridge_k3_graph.dist 3 5 : ℝ) * ((1 - α) / 2) := by
          simp [π, Fin.sum_univ_seven]
        rw [e, c4_bridge_k3_dist_zero_six]
        have c0 : (0 : ℝ) ≤ (1 - α) / 2 := by linarith
        have e1 : (c4_bridge_k3_graph.dist 1 4 : ℝ) ≤ 2 := by exact_mod_cast hd14
        have e2 : (c4_bridge_k3_graph.dist 3 5 : ℝ) ≤ 3 := by exact_mod_cast hd35
        nlinarith [mul_le_mul_of_nonneg_right e1 c0, mul_le_mul_of_nonneg_right e2 c0]
    · have hs0 := graph_idle_measure_sum_eq_one c4_bridge_k3_graph α 0 (by rw [hdeg0]; norm_num)
      have hs6 := graph_idle_measure_sum_eq_one c4_bridge_k3_graph α 6 (by rw [hdeg6]; norm_num)
      have hf : ∀ a b, (fun v => -(c4_bridge_k3_label v : ℝ)) a -
          (fun v => -(c4_bridge_k3_label v : ℝ)) b ≤ (c4_bridge_k3_graph.dist a b : ℝ) := by
        intro a b
        have := c4_bridge_k3_dist_ge b a
        rw [SimpleGraph.dist_comm] at this
        simp only
        linarith
      have := graph_wasserstein_dist_ge_of_lipschitz c4_bridge_k3_graph _ _
        (graph_idle_measure_nonneg c4_bridge_k3_graph α hα0.le hα1.le 0)
        (graph_idle_measure_nonneg c4_bridge_k3_graph α hα0.le hα1.le 6) hs0 hs6 _ hf
      have e0 : ∑ a, (fun v => -(c4_bridge_k3_label v : ℝ)) a *
          graph_idle_measure c4_bridge_k3_graph α 0 a = -(1 - α) := by
        simp +decide [Fin.sum_univ_seven, graph_idle_measure, hdeg0, c4_bridge_k3_label]
        ring
      have e6 : ∑ a, (fun v => -(c4_bridge_k3_label v : ℝ)) a *
          graph_idle_measure c4_bridge_k3_graph α 6 a = -(4 * α + 7 / 2 * (1 - α)) := by
        simp +decide [Fin.sum_univ_seven, graph_idle_measure, hdeg6, c4_bridge_k3_label]
        ring
      rw [e0, e6] at this
      linarith
  unfold graph_ollivier_curvature
  rw [hW, c4_bridge_k3_dist_zero_six]
  push_cast
  ring

theorem c4_bridge_k3_lly_lower_bound_four :
    3 / 8 ≤ graph_lly_curvature_lower_bound c4_bridge_k3_graph 4 := by
  have hconn := c4_bridge_k3_graph_connected
  have hall : ∀ v : Fin 7, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 := by decide
  have hd2 : ∀ v : Fin 7, c4_bridge_k3_graph.dist v 2 ≤ 2 ∧
      (v ≠ 0 → v ≠ 5 → v ≠ 6 → c4_bridge_k3_graph.dist v 2 ≤ 1) := by
    intro v
    rcases hall v with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨c4_bridge_k3_dist_le_two_three 0 1 2 (by decide) (by decide),
        fun h => absurd rfl h⟩
    · have := c4_bridge_k3_dist_le_of_adj 1 2 (by decide)
      exact ⟨by omega, fun _ _ _ => this⟩
    · simp
    · have := c4_bridge_k3_dist_le_of_adj 3 2 (by decide)
      exact ⟨by omega, fun _ _ _ => this⟩
    · have := c4_bridge_k3_dist_le_of_adj 4 2 (by decide)
      exact ⟨by omega, fun _ _ _ => this⟩
    · exact ⟨c4_bridge_k3_dist_le_two_three 5 4 2 (by decide) (by decide),
        fun _ h _ => absurd rfl h⟩
    · exact ⟨c4_bridge_k3_dist_le_two_three 6 4 2 (by decide) (by decide),
        fun _ _ h => absurd rfl h⟩
  have h56 := c4_bridge_k3_dist_le_of_adj 5 6 (by decide)
  have h65 := c4_bridge_k3_dist_le_of_adj 6 5 (by decide)
  unfold graph_lly_curvature_lower_bound
  refine le_csInf ⟨graph_lly_curvature c4_bridge_k3_graph 0 5, 0, 5, c4_bridge_k3_dist_zero_five, rfl⟩ ?_
  rintro κ ⟨x, y, hxy, rfl⟩
  have tri := hconn.dist_triangle (u := x) (v := 2) (w := y)
  rw [SimpleGraph.dist_comm (u := 2)] at tri
  obtain ⟨hx2, hx1⟩ := hd2 x
  obtain ⟨hy2, hy1⟩ := hd2 y
  have hx : x = 0 ∨ x = 5 ∨ x = 6 := by
    by_contra hc; push_neg at hc; have := hx1 hc.1 hc.2.1 hc.2.2; omega
  have hy : y = 0 ∨ y = 5 ∨ y = 6 := by
    by_contra hc; push_neg at hc; have := hy1 hc.1 hc.2.1 hc.2.2; omega
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · simp at hxy
  · rw [c4_bridge_k3_lly_zero_five]
  · rw [c4_bridge_k3_lly_zero_six]
  · rw [graph_lly_curvature_comm, c4_bridge_k3_lly_zero_five]
  · simp at hxy
  · omega
  · rw [graph_lly_curvature_comm, c4_bridge_k3_lly_zero_six]
  · omega
  · simp at hxy

theorem c4_bridge_k3_edge_connectivity_le_one :
    graph_edge_connectivity c4_bridge_k3_graph ≤ 1 := by
  have hnot : ¬ c4_bridge_k3_graph.IsEdgeConnected 2 := by
    rw [SimpleGraph.isEdgeConnected_two]
    intro h
    obtain ⟨p⟩ := h s(2, 4) 2 4
    have step : ∀ u v : Fin 7, c4_bridge_k3_graph.Adj u v → s(u, v) ≠ s(2, 4) →
        u.val < 4 → v.val < 4 := by decide
    have inv : ∀ {a b : Fin 7} (q : (c4_bridge_k3_graph.deleteEdges {s(2, 4)}).Walk a b),
        a.val < 4 → b.val < 4 := by
      intro a b q
      induction q with
      | nil => exact id
      | cons h q ih =>
        intro ha
        rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at h
        exact ih (step _ _ h.1 h.2 ha)
    exact absurd (inv p (by decide)) (by decide)
  unfold graph_edge_connectivity
  apply csSup_le ⟨0, SimpleGraph.IsEdgeConnected.zero⟩
  intro k hk
  by_contra hlt
  push_neg at hlt
  exact hnot (fun u v => (hk u v).anti hlt)

theorem not_edge_connectivity_ge_half_scale_mul_min_degree_mul_lly_lower_bound :
    ¬ ∀ d : ℕ, 3 ≤ d → ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected → d ≤ G.diam →
      ((d : ℝ) / 2) * (G.minDegree : ℝ) * graph_lly_curvature_lower_bound G d ≤
        (graph_edge_connectivity G : ℝ) := by
  intro h
  have hconn := c4_bridge_k3_graph_connected
  have hdiam : 4 ≤ c4_bridge_k3_graph.diam := by
    have := SimpleGraph.dist_le_diam (G := c4_bridge_k3_graph)
      (c4_bridge_k3_graph.connected_iff_ediam_ne_top.mp hconn) (u := 0) (v := 5)
    rw [c4_bridge_k3_dist_zero_five] at this
    exact this
  have := h 4 (by norm_num) c4_bridge_k3_graph hconn hdiam
  have hmin : c4_bridge_k3_graph.minDegree = 2 := by decide
  rw [hmin] at this
  have hk := c4_bridge_k3_lly_lower_bound_four
  have he : (graph_edge_connectivity c4_bridge_k3_graph : ℝ) ≤ 1 := by
    exact_mod_cast c4_bridge_k3_edge_connectivity_le_one
  push_cast at this
  nlinarith
