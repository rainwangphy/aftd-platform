import AFTD.Prelude
import AFTD.Kb.Tcs.OrderGraph
import AFTD.Kb.Tcs.OrderGraphServesUni

/-!
# order_graph_is_complete_uni

Topic: combinatorics   Node: 44c7f9436b5e

Provenance: formalization of a published result. Source: arXiv:2610.39311 Definition 3

An order graph G of dimension d is complete in the unidirectional model if for every subset S ⊆ Fin d and every element x : Fin d with x ∉ S, G serves requirement (S, x) in the unidirectional model.
-/

/-- An order graph G is complete in the unidirectional model if it serves every requirement (S, x) with x ∉ S in the unidirectional model. -/
def order_graph_is_complete_uni {d : ℕ} (G : OrderGraph d) : Prop := ∀ (S : Finset (Fin d)) (x : Fin d), x ∉ S → order_graph_serves_uni G S x
