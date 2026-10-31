import AFTD.Prelude
import AFTD.Kb.Tcs.Order
import AFTD.Kb.Tcs.OrderMoveToFront

/-!
# OrderGraph

Topic: combinatorics   Node: 24e5fbc3476c

Provenance: formalization of a published result. Source: arXiv:2610.39311 Definition 1

An order graph of dimension d is a structure consisting of a finite set V of orders of Fin d and a finite set E of edges (π, a) where π : Order d and a : Fin d, such that for each edge e ∈ E, the source e.1 is in V and the target order_move_to_front e.2 e.1 is in V.
-/

/-- An order graph of dimension d with finite vertex set V and edge set E. -/
structure OrderGraph (d : ℕ) where
  V : Finset (Order d)
  E : Finset (Order d × Fin d)
  edge_src : ∀ e ∈ E, e.1 ∈ V
  edge_tgt : ∀ e ∈ E, order_move_to_front e.2 e.1 ∈ V
