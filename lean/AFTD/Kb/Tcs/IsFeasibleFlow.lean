import AFTD.Prelude

/-!
# is_feasible_flow

Topic: online_algorithms   Node: 0aa1c574fd66

Provenance: formalization of a published result. Source: arXiv:2611.05669, Section 4.1

A signed flow F on Fin k is feasible for a demand vector a : Fin k → ℝ if F is skew-symmetric (F i j = -F j i for all i, j) and the net outgoing flow at each vertex i is ∑ j, F i j = a i.
-/

/-- A flow F is feasible for demand vector a if F is skew-symmetric and has divergence a. -/
def is_feasible_flow {k : ℕ} (F : Fin k → Fin k → ℝ) (a : Fin k → ℝ) : Prop := (∀ i j : Fin k, F i j = -F j i) ∧ (∀ i : Fin k, ∑ j : Fin k, F i j = a i)
