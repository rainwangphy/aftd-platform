import AFTD.Prelude

/-!
# arrival_routing_inflow_map

Topic: algorithms   Node: f06a7bb6fdfa

Provenance: formalization of a published result. Source: scout/2611-33785-a-polynomial-time-algorithm-for-arrival.md:182

For finite types V and S, a routing outflow function r : V → ℝ → Sum V S → ℝ, and departure counts z : V → ℝ, arrival_routing_inflow_map r z is the internal inflow vector in V → ℝ mapping each u : V to the sum over all v : V of r v (z v) (Sum.inl u).
-/

/-- Exact internal routing inflow map summing projected local outflows across all internal vertices. -/
noncomputable def arrival_routing_inflow_map
    {V S : Type*} [Fintype V]
    (r : V → ℝ → Sum V S → ℝ) (z : V → ℝ) : V → ℝ := fun u => ∑ v : V, r v (z v) (Sum.inl u)
