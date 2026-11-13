import AFTD.Prelude
import AFTD.Kb.Tcs.DirectedMultigraph
import AFTD.Kb.Tcs.DirectedDistENN

/-!
# SatisfiesC4

Topic: graphs   Node: 970381ca8014

Provenance: formalization of a published result. Source: arXiv:2611.12330 Section 3, Condition (C4)

Real-valued capacities u : E → ℝ and demands d : K → ℝ satisfy condition (C4) on topology (G, H) if for every binary edge-length function ℓ : E → ENNReal with ℓ e = 0 ∨ ℓ e = 1 for all e, the demand-weighted shortest path sum ∑ i, ENNReal.ofReal (d i) * directedDistENN G ℓ (H.src i) (H.tgt i) is at most the capacity-weighted sum ∑ e, ENNReal.ofReal (u e) * ℓ e.
-/

/-- Binary edge-length condition (C4) for directed multiflows. -/
noncomputable def SatisfiesC4 {V E K : Type*} [Fintype E] [Fintype K]
    (G : DirectedMultigraph V E) (H : DirectedMultigraph V K)
    (u : E → ℝ) (d : K → ℝ) : Prop :=
  ∀ ℓ : E → ENNReal, (∀ e, ℓ e = 0 ∨ ℓ e = 1) →
    (∑ i : K, ENNReal.ofReal (d i) * directedDistENN G ℓ (H.src i) (H.tgt i)) ≤
      (∑ e : E, ENNReal.ofReal (u e) * ℓ e)
