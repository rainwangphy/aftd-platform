import AFTD.Prelude
import AFTD.Kb.Tcs.GraphWassersteinDistGeOfLipschitz
import AFTD.Kb.Tcs.GraphDegreePosOfConnectedOfNe
import AFTD.Kb.Tcs.GraphIdleMeasureNonneg
import AFTD.Kb.Tcs.GraphIdleMeasureSumEqOne
import AFTD.Kb.Tcs.GraphOllivierCurvature
import AFTD.Kb.Tcs.GraphWassersteinDist
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphWassersteinDistMixDiracLe

/-!
# graph_ollivier_curvature_div_le_two_div_dist

Topic: graphs   Node: 20948cacda57

Provenance: helper lemma. Helper for graph_lly_curvature_le_two_div_dist (OP-164, arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature)).

In a finite connected graph, for x ≠ y and α ∈ [0, 1), κ_α(x, y)/(1 − α) ≤ 2/d(x, y).
-/

theorem graph_ollivier_curvature_div_le_two_div_dist {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (x y : V) (hxy : x ≠ y)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    graph_ollivier_curvature G α x y / (1 - α) ≤ 2 / (G.dist x y : ℝ) := by
  have hd : (0 : ℝ) < G.dist x y := by exact_mod_cast hG.pos_dist_of_ne hxy
  have hdx := graph_degree_pos_of_connected_of_ne G hG x y hxy
  have hdy := graph_degree_pos_of_connected_of_ne G hG y x hxy.symm
  have h1α : 0 < 1 - α := by linarith
  have hnx := graph_idle_measure_nonneg G α hα0 hα1.le x
  have hny := graph_idle_measure_nonneg G α hα0 hα1.le y
  have hsx := graph_idle_measure_sum_eq_one G α x hdx
  have hsy := graph_idle_measure_sum_eq_one G α y hdy
  have hf : ∀ a b, (fun v => (G.dist v y : ℝ)) a - (fun v => (G.dist v y : ℝ)) b ≤ G.dist a b := by
    intro a b
    have := hG.dist_triangle (u := a) (v := b) (w := y)
    simp only
    have : (G.dist a y : ℝ) ≤ G.dist a b + G.dist b y := by exact_mod_cast this
    linarith
  have hW := graph_wasserstein_dist_ge_of_lipschitz G _ _ hnx hny hsx hsy _ hf
  have ex : (G.dist x y : ℝ) - 1 + α ≤ ∑ a, (G.dist a y : ℝ) * graph_idle_measure G α x a := by
    have term : ∀ a, ((G.dist x y : ℝ) - 1 + (if a = x then 1 else 0)) * graph_idle_measure G α x a
        ≤ (G.dist a y : ℝ) * graph_idle_measure G α x a := by
      intro a
      by_cases hax : a = x
      · subst a; simp
      · simp only [hax, if_false, add_zero]
        by_cases hadj : G.Adj x a
        · apply mul_le_mul_of_nonneg_right _ (hnx a)
          have t := hG.dist_triangle (u := x) (v := a) (w := y)
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at t
          have : (G.dist x y : ℝ) ≤ 1 + G.dist a y := by exact_mod_cast t
          linarith
        · have : graph_idle_measure G α x a = 0 := by
            simp [graph_idle_measure, hax, hadj]
          rw [this]
          simp
    calc (G.dist x y : ℝ) - 1 + α
        = ∑ a, ((G.dist x y : ℝ) - 1 + (if a = x then 1 else 0)) * graph_idle_measure G α x a := by
          simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hsx, ite_mul, one_mul,
            zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
          simp [graph_idle_measure]
      _ ≤ _ := Finset.sum_le_sum fun a _ => term a
  have ey : ∑ a, (G.dist a y : ℝ) * graph_idle_measure G α y a = 1 - α := by
    have term : ∀ a, (G.dist a y : ℝ) * graph_idle_measure G α y a =
        graph_idle_measure G α y a - (if a = y then α else 0) := by
      intro a
      by_cases hay : a = y
      · subst a; simp [graph_idle_measure]
      · by_cases hadj : G.Adj y a
        · rw [SimpleGraph.dist_comm, SimpleGraph.dist_eq_one_iff_adj.mpr hadj]
          simp [hay]
        · simp [graph_idle_measure, hay, hadj]
    simp_rw [term]
    rw [Finset.sum_sub_distrib, hsy]
    simp
  have hWlow : (G.dist x y : ℝ) - 2 * (1 - α) ≤
      graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y) := by
    linarith
  unfold graph_ollivier_curvature
  rw [div_le_div_iff₀ h1α hd]
  have : graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y) /
      (G.dist x y : ℝ) * (G.dist x y : ℝ) =
      graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y) := by
    field_simp
  nlinarith
