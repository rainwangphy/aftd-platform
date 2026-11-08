import AFTD.Prelude

/-!
# simple_graph_is_k_connected

Topic: graphs   Node: 428c8de90a40

Provenance: formalization of a published result. Source: arXiv:2611.07145 Sec. 1

A finite simple graph G is k-connected if its order is strictly greater than k and the deletion of any subset of strictly fewer than k vertices leaves a connected graph.
-/

/-- A finite simple graph G is k-connected if its order is strictly greater than k and deleting strictly fewer than k vertices leaves a connected graph. -/
def simple_graph_is_k_connected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop := k < Fintype.card V ∧ ∀ (s : Finset V), s.card < k → (G.induce (s : Set V)ᶜ).Connected
