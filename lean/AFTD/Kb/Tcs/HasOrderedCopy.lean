import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# has_ordered_copy

Topic: graphs   Node: 9c8faf3bae80

Provenance: formalization of a published result. Source: arXiv:2611.08375 "New results on cyclic and ordered Ramsey numbers", Section 1

An ordered graph G contains an ordered copy of an ordered graph H if there exists a strictly monotone map f from the vertex set of H to that of G such that every edge of H maps to an edge of G.
-/

/-- An ordered graph G contains an ordered copy of H if there is an order-preserving edge-preserving map from V(H) to V(G). -/
def has_ordered_copy {α β : Type*} [LinearOrder α] [LinearOrder β]
    (G : SimpleGraph β) (H : SimpleGraph α) : Prop := ∃ f : α → β, StrictMono f ∧ ∀ ⦃u v : α⦄, H.Adj u v → G.Adj (f u) (f v)
