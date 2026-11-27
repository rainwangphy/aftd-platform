import AFTD.Prelude

/-!
# arrival_routing_projection

Topic: algorithms   Node: acdd6e7d1872

Provenance: formalization of a published result. Source: scout/2611-33785-a-polynomial-time-algorithm-for-arrival.md:146

The coordinate projection from the outflow space ℝ^(V ∪ S) to internal coordinates ℝ^V, sending w to w restricted to internal coordinates Sum.inl.
-/

/-- Coordinate projection from outflows on V ⊕ S to internal coordinates on V. -/
def arrival_routing_projection {V S : Type*} (w : Sum V S → ℝ) : V → ℝ := fun v => w (Sum.inl v)
