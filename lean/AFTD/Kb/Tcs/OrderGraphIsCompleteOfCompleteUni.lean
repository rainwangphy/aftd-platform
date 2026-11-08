import AFTD.Prelude
import AFTD.Kb.Tcs.OrderGraph
import AFTD.Kb.Tcs.OrderGraphIsComplete
import AFTD.Kb.Tcs.OrderGraphIsCompleteUni
import AFTD.Kb.Tcs.OrderGraphServes
import AFTD.Kb.Tcs.OrderGraphServesUni
import AFTD.Kb.Tcs.OrderMoveToFront
import AFTD.Kb.Tcs.Order

/-!
# order_graph_is_complete_of_complete_uni

Topic: combinatorics   Node: 8c48d71f302e

Provenance: helper lemma. arXiv:2610.39311 Definition 2

If an order graph G of dimension d is complete in the unidirectional model, then G is complete in the bidirectional model.
-/

/-- Every order graph that is complete in the unidirectional model is complete in the bidirectional model. -/
theorem order_graph_is_complete_of_complete_uni {d : ℕ} {G : OrderGraph d}
    (h : order_graph_is_complete_uni G) : order_graph_is_complete G := by
  intro S x hx
  obtain ⟨p, hp, hE, hchain, hlen, hlabels, hlast⟩ := h S x hx
  exact ⟨p, hp, hE, hchain, hlen, hlabels, Or.inr hlast⟩
