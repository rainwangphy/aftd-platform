import AFTD.Prelude

/-!
# is_geometric_gibbs_critical_q0

Topic: quantum_mechanics   Node: 9376a3e78ac9

Provenance: formalization of a published result. Source: arXiv:2610.35433

A parameter q is the critical value q_0 if 0 < q < 1 and q^3 * (1 + q)^2 = 1.
-/

/-- Predicate for the critical value q_0 in (0, 1) solving q_0^3(1+q_0)^2 = 1. -/
def is_geometric_gibbs_critical_q0 (q : ℝ) : Prop := 0 < q ∧ q < 1 ∧ q ^ 3 * (1 + q) ^ 2 = 1
