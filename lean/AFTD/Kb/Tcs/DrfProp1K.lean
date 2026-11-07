import AFTD.Prelude

/-!
# drf_prop1_k

Topic: online_algorithms   Node: 8291e982b7cb

Provenance: formalization of a published result. Source: arXiv:2611.07905 Proposition 1

In the lower-bound instance with D resources and parameter m, the number of shared jobs demanding all resources is k = floor(m * sqrt(D)).
-/

/-- The number of jobs demanding all resources in the lower-bound instance with D resources and parameter m. -/
noncomputable def drf_prop1_k (D m : ℕ) : ℕ := Nat.floor ((m : ℝ) * Real.sqrt (D : ℝ))
