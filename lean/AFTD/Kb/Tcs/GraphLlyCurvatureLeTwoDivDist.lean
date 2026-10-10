import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.Tcs.GraphWassersteinDistGeOfLipschitz
import AFTD.Kb.Tcs.GraphOllivierCurvature
import AFTD.Kb.Tcs.GraphOllivierCurvatureDivLeTwoDivDist
import AFTD.Kb.Tcs.GraphLlyCurvatureTendsto

/-!
# graph_lly_curvature_le_two_div_dist

Topic: graphs   Node: 9617faef44cd

Provenance: helper lemma. Helper for OP-164 (arXiv:2610.10559). The 1-Lipschitz function v ↦ d(v, y) gives W(μ_x^α, μ_y^α) ≥ d − 2(1 − α), hence κ_α ≤ 2(1 − α)/d; passing to the limit needs its existence (Sec. 2.2 of the paper: κ_α/(1 − α) is nondecreasing and bounded).

For distinct vertices x, y of a finite connected graph, κ_LLY(x, y) ≤ 2/d(x, y).
-/

theorem graph_lly_curvature_le_two_div_dist {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (x y : V) (hxy : x ≠ y) :
    graph_lly_curvature G x y ≤ 2 / (G.dist x y : ℝ) := by
  apply le_of_tendsto (graph_lly_curvature_tendsto G hG x y hxy)
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with α hα
  exact graph_ollivier_curvature_div_le_two_div_dist G hG x y hxy α hα.1.le hα.2
