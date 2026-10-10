import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.Tcs.GraphOllivierCurvature

/-!
# graph_lly_curvature_eq_of_ollivier_eq

Topic: graphs   Node: ff294f2d0a43

Provenance: helper lemma. Helper for the refutation of OP-165 (arXiv:2610.10559, after Theorem 1.4).

If κ_α(x, y) = (1 − α)c for all α in an interval (a, 1), then κ_LLY(x, y) = c.
-/

theorem graph_lly_curvature_eq_of_ollivier_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (c a : ℝ) (ha : a < 1)
    (h : ∀ α, a < α → α < 1 → graph_ollivier_curvature G α x y = (1 - α) * c) :
    graph_lly_curvature G x y = c := by
  unfold graph_lly_curvature
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsLT ha] with α hα
  rw [h α hα.1 hα.2]
  have : (1 - α) ≠ 0 := sub_ne_zero.mpr hα.2.ne'
  field_simp
