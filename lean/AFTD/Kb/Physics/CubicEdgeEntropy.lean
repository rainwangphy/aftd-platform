import AFTD.Prelude

/-!
# cubic_edge_entropy

Topic: statistical_mechanics   Node: 534739d0311a

Provenance: formalization of a published result. Source: arXiv:2204.00875

The entropy production contribution phi(x) of an edge carrying stationary current x under unit total forward-plus-reverse flux is |x| * Real.log ((1 + |x|) / (1 - |x|)).
-/

/-- Entropy-production contribution of an edge carrying stationary current x. -/
noncomputable def cubic_edge_entropy (x : ℝ) : ℝ := |x| * Real.log ((1 + |x|) / (1 - |x|))
