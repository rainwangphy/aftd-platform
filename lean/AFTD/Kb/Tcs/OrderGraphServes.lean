import AFTD.Prelude
import AFTD.Kb.Tcs.OrderGraph
import AFTD.Kb.Tcs.OrderMoveToFront
import AFTD.Kb.Tcs.Order

/-!
# order_graph_serves

Topic: combinatorics   Node: f09d7ca9dd8f

Provenance: formalization of a published result. Source: arXiv:2610.39311 Definition 2

An order graph G serves requirement (S, x) where S is a finite set of Fin d and x : Fin d if there exists a nonempty list of edges p all in G.E, chaining by e2.1 = order_move_to_front e1.2 e1.1, such that p has length |S| + 1, the set of edge labels in p is insert x S, and either the first edge of p or the last edge of p has label x.
-/

/-- G serves requirement (S, x) in the bidirectional model. -/
def order_graph_serves {d : ℕ} (G : OrderGraph d) (S : Finset (Fin d)) (x : Fin d) : Prop := ∃ (p : List (Order d × Fin d)) (hp : p ≠ []),
    (∀ e ∈ p, e ∈ G.E) ∧
    p.IsChain (fun e1 e2 => e2.1 = order_move_to_front e1.2 e1.1) ∧
    p.length = S.card + 1 ∧
    (p.map Prod.snd).toFinset = insert x S ∧
    ((p.head hp).2 = x ∨ (p.getLast hp).2 = x)
