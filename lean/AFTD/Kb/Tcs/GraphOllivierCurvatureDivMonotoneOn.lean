import AFTD.Prelude
import AFTD.Kb.Tcs.GraphWassersteinDistMixDiracLe
import AFTD.Kb.Tcs.GraphIdleMeasureEqMix
import AFTD.Kb.Tcs.GraphDegreePosOfConnectedOfNe
import AFTD.Kb.Tcs.GraphIdleMeasureNonneg
import AFTD.Kb.Tcs.GraphIdleMeasureSumEqOne
import AFTD.Kb.Tcs.GraphOllivierCurvature
import AFTD.Kb.Tcs.GraphWassersteinDist
import AFTD.Kb.Tcs.GraphIdleMeasure

/-!
# graph_ollivier_curvature_div_monotoneOn

Topic: graphs   Node: ecc7d9dead11

Provenance: formalization of a published result. Source: arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Sec. 2.2 (the monotonicity of κ_α/(1 − α) on which Definition 2.3 rests, quoted there from its reference [15]); proved here by mixing transport plans with the point masses at idleness 1 instead of through concavity.

In a finite connected graph, for x ≠ y, α ↦ κ_α(x, y)/(1 − α) is nondecreasing on (0, 1).
-/

theorem graph_ollivier_curvature_div_monotoneOn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (x y : V) (hxy : x ≠ y) :
    MonotoneOn (fun α => graph_ollivier_curvature G α x y / (1 - α)) (Set.Ioo 0 1) := by
  intro α hα β hβ hab
  simp only
  have hd : (0 : ℝ) < G.dist x y := by exact_mod_cast hG.pos_dist_of_ne hxy
  have hdx := graph_degree_pos_of_connected_of_ne G hG x y hxy
  have hdy := graph_degree_pos_of_connected_of_ne G hG y x hxy.symm
  have h1α : 0 < 1 - α := by linarith [hα.2]
  have h1β : 0 < 1 - β := by linarith [hβ.2]
  have ht0 : 0 ≤ (1 - β) / (1 - α) := div_nonneg h1β.le h1α.le
  have ht1 : (1 - β) / (1 - α) ≤ 1 := by rw [div_le_one h1α]; linarith
  have hmix := graph_wasserstein_dist_mix_dirac_le G (graph_idle_measure G α x)
    (graph_idle_measure G α y) (graph_idle_measure_nonneg G α hα.1.le hα.2.le x)
    (graph_idle_measure_nonneg G α hα.1.le hα.2.le y) (graph_idle_measure_sum_eq_one G α x hdx)
    (graph_idle_measure_sum_eq_one G α y hdy) x y _ ht0 ht1
  rw [← graph_idle_measure_eq_mix G x α β hα.2, ← graph_idle_measure_eq_mix G y α β hα.2] at hmix
  unfold graph_ollivier_curvature
  generalize graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y) = A at hmix ⊢
  generalize graph_wasserstein_dist G (graph_idle_measure G β x) (graph_idle_measure G β y) = B at hmix ⊢
  generalize (G.dist x y : ℝ) = d at hmix hd ⊢
  have hB : B * (1 - α) ≤ (1 - β) * A + (β - α) * d := by
    have := mul_le_mul_of_nonneg_right hmix h1α.le
    have e1 : (1 - β) / (1 - α) * A * (1 - α) = (1 - β) * A := by field_simp
    have e2 : (1 - (1 - β) / (1 - α)) * d * (1 - α) = (β - α) * d := by field_simp; ring
    nlinarith [e1, e2]
  rw [div_le_div_iff₀ h1α h1β]
  have lhs : (1 - A / d) * (1 - β) = ((d - A) * (1 - β)) / d := by field_simp
  have rhs : (1 - B / d) * (1 - α) = ((d - B) * (1 - α)) / d := by field_simp
  rw [lhs, rhs]
  apply div_le_div_of_nonneg_right _ hd.le
  nlinarith
