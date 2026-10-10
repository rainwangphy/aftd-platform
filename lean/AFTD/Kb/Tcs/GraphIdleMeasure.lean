import AFTD.Prelude

/-!
# graph_idle_measure

Topic: graphs   Node: 55411ec07d4a

Provenance: formalization of a published result. Source: arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Sec. 2.2 (the measure μ_x^α).

The lazy random-walk measure μ_x^α at x with idleness α: mass α at x, (1 − α)/d_x at each neighbour of x, 0 elsewhere.
-/

/-- The measure `μ_x^α`: `α` at `x`, `(1 - α)/deg x` on each neighbour of `x`, `0` elsewhere. -/
noncomputable def graph_idle_measure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (x : V) : V → ℝ :=
  fun v => if v = x then α else if G.Adj x v then (1 - α) / (G.degree x : ℝ) else 0
