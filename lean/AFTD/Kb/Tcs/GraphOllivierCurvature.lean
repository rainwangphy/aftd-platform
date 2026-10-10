import AFTD.Prelude
import AFTD.Kb.Tcs.GraphWassersteinDist
import AFTD.Kb.Tcs.GraphIdleMeasure

/-!
# graph_ollivier_curvature

Topic: graphs   Node: 7723736545d0

Provenance: formalization of a published result. Source: arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Definition 2.2 (Ollivier–Ricci curvature).

The α-Ollivier–Ricci curvature κ_α(x, y) = 1 − W(μ_x^α, μ_y^α)/d(x, y).
-/

/-- α-Ollivier–Ricci curvature `κ_α(x, y) = 1 - W(μ_x^α, μ_y^α) / d(x, y)`. -/
noncomputable def graph_ollivier_curvature {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (x y : V) : ℝ :=
  1 - graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y) /
    (G.dist x y : ℝ)
