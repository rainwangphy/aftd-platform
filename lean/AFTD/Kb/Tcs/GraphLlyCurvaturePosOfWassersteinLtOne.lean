import AFTD.Prelude
import AFTD.Kb.Tcs.GraphOllivierCurvatureDivMonotoneOn
import AFTD.Kb.Tcs.GraphLlyCurvatureTendsto
import AFTD.Kb.Tcs.GraphOllivierCurvature
import AFTD.Kb.Tcs.GraphWassersteinDist
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphLlyCurvature

/-!
# graph_lly_curvature_pos_of_wasserstein_lt_one

Topic: graphs   Node: f0d06b669fd0

Provenance: helper lemma. step towards lly_curvature_pos_of_edge_connectivity_ge

If the Wasserstein distance between the lazy random-walk measures μ_x^α and μ_y^α on an edge xy is strictly less than 1 for some α ∈ (0, 1), then the Lin–Lu–Yau curvature κ_LLY(x, y) is strictly positive.
-/

/-- If the Wasserstein distance between idle measures μ_x^α and μ_y^α is strictly less than 1 for some α ∈ (0, 1) along an edge xy, then the Lin–Lu–Yau curvature κ_LLY(x, y) is strictly positive. -/
theorem graph_lly_curvature_pos_of_wasserstein_lt_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (x y : V) (hxy : G.Adj x y)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hW : graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y) < 1) :
    0 < graph_lly_curvature G x y := by
  have hne : x ≠ y := hxy.ne
  have hdist : G.dist x y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxy
  have hdistR : (G.dist x y : ℝ) = 1 := by rw [hdist]; norm_num
  have hcurv : graph_ollivier_curvature G α x y =
      1 - graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y) := by
    unfold graph_ollivier_curvature
    rw [hdistR]
    simp
  have hposcurv : 0 < graph_ollivier_curvature G α x y := by
    rw [hcurv]; linarith
  have hposf : 0 < graph_ollivier_curvature G α x y / (1 - α) := by
    apply div_pos hposcurv; linarith
  have hmono := graph_ollivier_curvature_div_monotoneOn G hG x y hne
  have htend := graph_lly_curvature_tendsto G hG x y hne
  have hev : ∀ᶠ β in nhdsWithin 1 (Set.Iio 1),
      graph_ollivier_curvature G α x y / (1 - α) ≤
        graph_ollivier_curvature G β x y / (1 - β) := by
    apply Filter.eventually_of_mem
    · exact mem_nhdsWithin.mpr ⟨Set.Ioi α, isOpen_Ioi, hα1, fun z hz => hz⟩
    · intro β hβ
      exact hmono ⟨hα0, hα1⟩ ⟨lt_trans hα0 hβ.1, hβ.2⟩ (le_of_lt hβ.1)
  have hle : graph_ollivier_curvature G α x y / (1 - α) ≤ graph_lly_curvature G x y :=
    ge_of_tendsto htend hev
  linarith
