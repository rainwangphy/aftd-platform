import AFTD.Prelude
import AFTD.Kb.Tcs.DirectedMultigraph

/-!
# IsFeasibleMultiflow

Topic: graphs   Node: a5a6dfe38fff

Provenance: formalization of a published result. Source: arXiv:2611.12330 Section 2

A multicommodity flow function f : K → E → ℝ is feasible for capacities u : E → ℝ and demands d : K → ℝ on topology (G, H) if f is non-negative, total flow on each edge is at most capacity, and net outflow at each vertex equals source demand minus sink demand.
-/

/-- Feasibility of a multiflow: nonnegativity, capacity bounds, and vertex conservation equations. -/
def IsFeasibleMultiflow {V E K : Type*} [Fintype E] [Fintype K] [DecidableEq V]
    (G : DirectedMultigraph V E) (H : DirectedMultigraph V K)
    (u : E → ℝ) (d : K → ℝ) (f : K → E → ℝ) : Prop :=
  (∀ i e, 0 ≤ f i e) ∧
  (∀ e, (∑ i : K, f i e) ≤ u e) ∧
  (∀ i v, (∑ e : E, if G.src e = v then f i e else 0) - (∑ e : E, if G.tgt e = v then f i e else 0) =
    (if H.src i = v then d i else 0) - (if H.tgt i = v then d i else 0))
