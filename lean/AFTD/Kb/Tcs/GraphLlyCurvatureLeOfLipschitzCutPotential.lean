import AFTD.Prelude
import AFTD.Kb.Tcs.GraphWassersteinDistGeOfLipschitz
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphLlyCurvatureTendsto
import AFTD.Kb.Tcs.GraphDegreePosOfConnectedOfNe
import AFTD.Kb.Tcs.GraphIdleMeasureSumEqOne
import AFTD.Kb.Tcs.GraphOllivierCurvature
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.Tcs.GraphIdleMeasureNonneg
import AFTD.Kb.Tcs.GraphWassersteinDist

/-!
# graph_lly_curvature_le_of_lipschitz_cut_potential

Topic: graphs   Node: ab55d372d7fc

Provenance: helper lemma. step towards exists_dist_three_lly_curvature_le_cut

Kantorovich-duality bound on the Lin–Lu–Yau curvature at a pair: for x ≠ y and any 1-Lipschitz potential f with f(x) − f(y) = d(x,y), κ_LLY(x,y) ≤ (d − A_x + A_y)/d, where A_z is the average of f over the neighbourhood of z.
-/

/-- Kantorovich-duality (1-Lipschitz potential) upper bound for the Lin–Lu–Yau curvature at a pair of distinct vertices. -/
theorem graph_lly_curvature_le_of_lipschitz_cut_potential
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (x y : V) (hxy : x ≠ y) (f : V → ℝ)
    (hf : ∀ a b : V, f a - f b ≤ (G.dist a b : ℝ))
    (hval : f x - f y = (G.dist x y : ℝ)) :
    graph_lly_curvature G x y ≤
      ((G.dist x y : ℝ) - (∑ a ∈ G.neighborFinset x, f a) / (G.degree x : ℝ)
        + (∑ b ∈ G.neighborFinset y, f b) / (G.degree y : ℝ)) / (G.dist x y : ℝ) := by
  have hd : (0 : ℝ) < G.dist x y := by exact_mod_cast hG.pos_dist_of_ne hxy
  have hdx : 0 < G.degree x := graph_degree_pos_of_connected_of_ne G hG x y hxy
  have hdy : 0 < G.degree y := graph_degree_pos_of_connected_of_ne G hG y x hxy.symm
  have sumid : ∀ (z : V), 0 < G.degree z → ∀ α : ℝ,
      ∑ a, f a * graph_idle_measure G α z a
        = α * f z + (1 - α) * ((∑ a ∈ G.neighborFinset z, f a) / (G.degree z : ℝ)) := by
    intro z hz α
    have hd_ne : (G.degree z : ℝ) ≠ 0 := by positivity
    have step1 : ∑ a, f a * graph_idle_measure G α z a
        = f z * α + ∑ a ∈ (Finset.univ.erase z), f a * (if G.Adj z a then (1 - α) / (G.degree z : ℝ) else 0) := by
      rw [← Finset.add_sum_erase Finset.univ (fun a => f a * graph_idle_measure G α z a) (Finset.mem_univ z)]
      congr 1
      · simp [graph_idle_measure]
      · apply Finset.sum_congr rfl
        intro a ha
        have haz : a ≠ z := (Finset.mem_erase.mp ha).1
        simp [graph_idle_measure, haz]
    have step2 : ∑ a ∈ (Finset.univ.erase z), f a * (if G.Adj z a then (1 - α) / (G.degree z : ℝ) else 0)
        = (1 - α) / (G.degree z : ℝ) * ∑ a ∈ (Finset.univ.erase z), (if G.Adj z a then f a else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : G.Adj z a <;> simp [h, mul_comm]
    have step3 : ∑ a ∈ (Finset.univ.erase z), (if G.Adj z a then f a else 0) = ∑ a ∈ G.neighborFinset z, f a := by
      have h1 : ∑ a, (if G.Adj z a then f a else 0) = ∑ a ∈ G.neighborFinset z, f a := by
        rw [← Finset.sum_filter, SimpleGraph.neighborFinset_eq_filter]
      have h2 : (if G.Adj z z then f z else 0) + ∑ a ∈ (Finset.univ.erase z), (if G.Adj z a then f a else 0)
          = ∑ a, (if G.Adj z a then f a else 0) :=
        Finset.add_sum_erase Finset.univ (fun a => if G.Adj z a then f a else 0) (Finset.mem_univ z)
      rw [← h2] at h1
      simp only [SimpleGraph.irrefl, if_false, zero_add] at h1
      exact h1
    rw [step1, step2, step3]
    field_simp
  have key : ∀ α : ℝ, 0 ≤ α → α < 1 →
      graph_ollivier_curvature G α x y / (1 - α) ≤
        ((G.dist x y : ℝ) - (∑ a ∈ G.neighborFinset x, f a) / (G.degree x : ℝ)
          + (∑ b ∈ G.neighborFinset y, f b) / (G.degree y : ℝ)) / (G.dist x y : ℝ) := by
    intro α hα0 hα1
    have h1α : 0 < 1 - α := by linarith
    have hnx := graph_idle_measure_nonneg G α hα0 hα1.le x
    have hny := graph_idle_measure_nonneg G α hα0 hα1.le y
    have hsx := graph_idle_measure_sum_eq_one G α x hdx
    have hsy := graph_idle_measure_sum_eq_one G α y hdy
    have hW := graph_wasserstein_dist_ge_of_lipschitz G (graph_idle_measure G α x) (graph_idle_measure G α y)
      hnx hny hsx hsy f hf
    rw [sumid x hdx α, sumid y hdy α] at hW
    have hWlow : (G.dist x y : ℝ) - (1 - α) * ((G.dist x y : ℝ)
        - (∑ a ∈ G.neighborFinset x, f a) / (G.degree x : ℝ)
        + (∑ b ∈ G.neighborFinset y, f b) / (G.degree y : ℝ)) ≤
        graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y) := by
      nlinarith [hW, hval]
    unfold graph_ollivier_curvature
    rw [div_le_div_iff₀ h1α hd]
    have hsimp : (1 - graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y) / (G.dist x y : ℝ)) * (G.dist x y : ℝ)
        = (G.dist x y : ℝ) - graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y) := by
      field_simp
    rw [hsimp]
    nlinarith [hWlow]
  apply le_of_tendsto (graph_lly_curvature_tendsto G hG x y hxy)
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with α hα
  exact key α hα.1.le hα.2
