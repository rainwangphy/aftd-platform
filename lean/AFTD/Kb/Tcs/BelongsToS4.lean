import AFTD.Prelude
import AFTD.Kb.Tcs.DirectedMultigraph
import AFTD.Kb.Tcs.SatisfiesC4
import AFTD.Kb.Tcs.HasFeasibleMultiflow

/-!
# BelongsToS4

Topic: graphs   Node: 90c52d816232

Provenance: formalization of a published result. Source: arXiv:2611.12330 Definition 1

A directed multiflow topology (G, H) belongs to S_4 if for every non-negative capacities u : E → ℝ and demands d : K → ℝ, satisfying condition (C4) implies the existence of a feasible multiflow.
-/

/-- Class S_4 of directed multiflow topologies where condition (C4) implies feasibility. -/
def BelongsToS4 {V E K : Type*} [Fintype E] [Fintype K] [DecidableEq V]
    (G : DirectedMultigraph V E) (H : DirectedMultigraph V K) : Prop :=
  ∀ (u : E → ℝ) (d : K → ℝ), (∀ e, 0 ≤ u e) → (∀ i, 0 ≤ d i) →
    SatisfiesC4 G H u d → HasFeasibleMultiflow G H u d
