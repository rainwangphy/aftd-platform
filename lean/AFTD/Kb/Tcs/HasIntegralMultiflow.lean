import AFTD.Prelude
import AFTD.Kb.Tcs.DirectedMultigraph
import AFTD.Kb.Tcs.IsFeasibleMultiflow

/-!
# HasIntegralMultiflow

Topic: graphs   Node: a9b4877f6974

Provenance: formalization of a published result. Source: arXiv:2611.12330 Section 2

An instance (G, H, u, d) has an integral multiflow if there exists a feasible multiflow f : K → E → ℝ such that every f i e is a natural number.
-/

/-- Existence of a feasible integral multiflow for an instance (G, H, u, d). -/
def HasIntegralMultiflow {V E K : Type*} [Fintype E] [Fintype K] [DecidableEq V]
    (G : DirectedMultigraph V E) (H : DirectedMultigraph V K)
    (u : E → ℝ) (d : K → ℝ) : Prop :=
  ∃ f : K → E → ℝ, IsFeasibleMultiflow G H u d f ∧ ∀ i e, ∃ n : ℕ, f i e = n
