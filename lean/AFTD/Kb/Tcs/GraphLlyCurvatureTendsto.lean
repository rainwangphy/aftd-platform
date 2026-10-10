import AFTD.Prelude
import AFTD.Kb.Tcs.GraphOllivierCurvatureDivMonotoneOn
import AFTD.Kb.Tcs.GraphOllivierCurvatureDivLeTwoDivDist
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.Tcs.GraphOllivierCurvature

/-!
# graph_lly_curvature_tendsto

Topic: graphs   Node: fccac5ff5f7f

Provenance: formalization of a published result. Source: arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Sec. 2.2: existence of the limit in Definition 2.3 (quoted there from its reference [15]); finite connected graphs.

In a finite connected graph, for x ≠ y, κ_α(x, y)/(1 − α) converges as α → 1⁻, to κ_LLY(x, y): the limit in the definition of the Lin–Lu–Yau curvature exists.
-/

theorem graph_lly_curvature_tendsto {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (x y : V) (hxy : x ≠ y) :
    Filter.Tendsto (fun α => graph_ollivier_curvature G α x y / (1 - α))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (graph_lly_curvature G x y)) := by
  have h := MonotoneOn.tendsto_nhdsWithin_Ioo_left (y := (0 : ℝ)) (x := 1)
    ⟨1 / 2, by norm_num, by norm_num⟩ (graph_ollivier_curvature_div_monotoneOn G hG x y hxy)
    ⟨2 / (G.dist x y : ℝ), by
      rintro _ ⟨α, hα, rfl⟩
      exact graph_ollivier_curvature_div_le_two_div_dist G hG x y hxy α hα.1.le hα.2⟩
  unfold graph_lly_curvature
  rw [h.limUnder_eq]
  exact h
