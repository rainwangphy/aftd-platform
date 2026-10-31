import AFTD.Prelude
import AFTD.Kb.Tcs.OrderGraph
import AFTD.Kb.Tcs.Order
import AFTD.Kb.Tcs.OrderPos

/-!
# order_graph_edges_ge

Topic: combinatorics   Node: 82fc4ff07605

Provenance: formalization of a published result. Source: arXiv:2610.39311 Theorem 6

Given an order graph G of dimension d and a natural number m, order_graph_edges_ge G m is the subset of edges e ∈ G.E such that m ≤ order_pos e.1 e.2.
-/

/-- The set of edges (ν, a) in G with pos_ν(a) ≥ m. -/
def order_graph_edges_ge {d : ℕ} (G : OrderGraph d) (m : ℕ) : Finset (Order d × Fin d) := G.E.filter (fun e => m ≤ order_pos e.1 e.2)
