import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIdleMeasure

/-!
# graph_idle_measure_eq_mix

Topic: graphs   Node: 9451d825249f

Provenance: helper lemma. Helper for graph_lly_curvature_le_two_div_dist (OP-164, arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature)).

For α < 1 and any β, μ_x^β = λ μ_x^α + (1 − λ) δ_x with λ = (1 − β)/(1 − α).
-/

theorem graph_idle_measure_eq_mix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (α β : ℝ) (hα : α < 1) :
    graph_idle_measure G β x = fun v => (1 - β) / (1 - α) * graph_idle_measure G α x v +
      (1 - (1 - β) / (1 - α)) * (if v = x then 1 else 0) := by
  have hne : (1 - α) ≠ 0 := by linarith
  funext v
  unfold graph_idle_measure
  by_cases hvx : v = x
  · simp only [hvx, if_true]
    field_simp
    ring
  · simp only [hvx, if_false, mul_zero, add_zero]
    by_cases hadj : G.Adj x v
    · simp only [hadj, if_true]
      by_cases hD : (G.degree x : ℝ) = 0
      · simp [hD]
      · field_simp
    · simp [hadj]
