import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvature

/-!
# graph_lly_curvature_lower_bound

Topic: graphs   Node: c76de5f666a8

Provenance: formalization of a published result. Source: arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Definition 2.4 (lower Lin–Lu–Yau curvature bound at scale i).

The lower Lin–Lu–Yau curvature bound at scale i: κ_LLY^(i)(G) = inf { κ_LLY(x, y) : d(x, y) = i }.
-/

/-- `κ_LLY^(i)(G)`: the infimum of the Lin–Lu–Yau curvature over pairs of vertices at distance `i`. -/
noncomputable def graph_lly_curvature_lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : ℕ) : ℝ :=
  sInf {κ | ∃ x y : V, G.dist x y = i ∧ graph_lly_curvature G x y = κ}
