import AFTD.Prelude
import AFTD.Kb.Tcs.OrderGraph
import AFTD.Kb.Tcs.OrderGraphServes

/-!
# order_graph_is_complete

Topic: combinatorics   Node: d8a56dcb3780

Provenance: formalization of a published result. Source: arXiv:2610.39311 Definition 3

An order graph G is complete in the bidirectional model if for every subset S ⊆ Fin d and every element x : Fin d with x ∉ S, G serves requirement (S, x).
-/

/-- An order graph is complete if it serves every requirement (S, x). -/
def order_graph_is_complete {d : ℕ} (G : OrderGraph d) : Prop := ∀ (S : Finset (Fin d)) (x : Fin d), x ∉ S → order_graph_serves G S x
