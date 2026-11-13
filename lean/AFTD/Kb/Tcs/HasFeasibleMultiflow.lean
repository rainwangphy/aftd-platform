import AFTD.Prelude
import AFTD.Kb.Tcs.DirectedMultigraph
import AFTD.Kb.Tcs.IsFeasibleMultiflow

/-!
# HasFeasibleMultiflow

Topic: graphs   Node: 06be082a31c0

Provenance: formalization of a published result. Source: arXiv:2611.12330 Section 2

An instance (G, H, u, d) has a feasible multiflow if there exists some flow function f : K → E → ℝ satisfying IsFeasibleMultiflow G H u d f.
-/

/-- Existence of a feasible multiflow for an instance (G, H, u, d). -/
def HasFeasibleMultiflow {V E K : Type*} [Fintype E] [Fintype K] [DecidableEq V]
    (G : DirectedMultigraph V E) (H : DirectedMultigraph V K)
    (u : E → ℝ) (d : K → ℝ) : Prop :=
  ∃ f : K → E → ℝ, IsFeasibleMultiflow G H u d f
