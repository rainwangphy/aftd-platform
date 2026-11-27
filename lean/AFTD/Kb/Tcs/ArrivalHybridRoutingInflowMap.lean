import AFTD.Prelude

/-!
# arrival_hybrid_routing_inflow_map

Topic: algorithms   Node: 5059a715c296

Provenance: formalization of a published result. Source: scout/2611-33785-a-polynomial-time-algorithm-for-arrival.md:182

For finite types V and S, period lengths d : V → ℕ, multiplicity vectors m : V → Sum V S → ℝ, local routing rules r : V → ℝ → Sum V S → ℝ, restored period sets W : V → Finset ℕ, and departure counts z : V → ℝ, arrival_hybrid_routing_inflow_map d m r W z is the internal inflow vector in V → ℝ mapping each u : V to the sum over all v : V of (if Nat.floor (z v / (d v : ℝ)) ∈ W v then r v (z v) else (z v / (d v : ℝ)) • m v) (Sum.inl u).
-/

/-- Hybrid internal routing inflow map summing projected hybrid local outflows across all internal vertices. -/
noncomputable def arrival_hybrid_routing_inflow_map
    {V S : Type*} [Fintype V]
    (d : V → ℕ) (m : V → Sum V S → ℝ) (r : V → ℝ → Sum V S → ℝ) (W : V → Finset ℕ) (z : V → ℝ) : V → ℝ := fun u => ∑ v : V,
    (if Nat.floor (z v / (d v : ℝ)) ∈ W v then r v (z v) else (z v / (d v : ℝ)) • m v) (Sum.inl u)
