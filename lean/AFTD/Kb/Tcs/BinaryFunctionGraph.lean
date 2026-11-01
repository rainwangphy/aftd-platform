import AFTD.Prelude

/-!
# binary_function_graph

Topic: graphs   Node: 40075c555ba8

Provenance: formalization of a published result. Source: arXiv:2610.37920 Section 2

The binary function graph of a simple graph G is the graph with vertices V → Bool, where two distinct functions f and g are adjacent if and only if for each boolean value b, the set of vertices where both functions evaluate to b is an independent set in G.
-/

/-- The binary function graph of a simple graph G, whose vertices are binary functions on V(G). -/
def binary_function_graph {V : Type*} (G : SimpleGraph V) : SimpleGraph (V → Bool) where
  Adj f g := f ≠ g ∧ ∀ b : Bool, G.IsIndepSet {v | f v = b ∧ g v = b}
  symm := ⟨fun f g ⟨hne, hind⟩ => ⟨hne.symm, fun b => by simpa [and_comm] using hind b⟩⟩
  loopless := ⟨fun f ⟨hne, _⟩ => hne rfl⟩
