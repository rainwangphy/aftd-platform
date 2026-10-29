import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHypercube

/-!
# is_hypercube_square

Topic: combinatorics   Node: 4563834e1687

Provenance: formalization of a published result. Source: arXiv:2610.36461 Section 2.1

A subset of 4 vertices in the hypercube Q_n is a square if its induced subgraph is isomorphic to the 4-cycle C_4.
-/

/-- A square in Q_n is a 4-vertex subset inducing a 4-cycle. -/
def is_hypercube_square (n : ℕ) (sq : Finset (Fin n → Bool)) : Prop :=
  sq.card = 4 ∧ Nonempty (((simple_graph_hypercube n).induce (sq : Set (Fin n → Bool))) ≃g SimpleGraph.cycleGraph 4)
