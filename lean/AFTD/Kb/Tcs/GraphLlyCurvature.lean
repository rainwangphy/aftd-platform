import AFTD.Prelude
import AFTD.Kb.Tcs.GraphOllivierCurvature

/-!
# graph_lly_curvature

Topic: graphs   Node: 248c3ecab563

Provenance: formalization of a published result. Source: arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Definition 2.3 (Lin–Lu–Yau curvature); the limit is written with `Filter.limUnder`, which agrees with it since the limit exists (Sec. 2.2).

The Lin–Lu–Yau curvature κ_LLY(x, y) = lim_{α → 1⁻} κ_α(x, y)/(1 − α).
-/

/-- Lin–Lu–Yau curvature: the limit of `κ_α(x, y) / (1 - α)` as the idleness `α` tends to `1` from below. -/
noncomputable def graph_lly_curvature {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : ℝ :=
  Filter.limUnder (nhdsWithin 1 (Set.Iio 1)) (fun α => graph_ollivier_curvature G α x y / (1 - α))
