import AFTD.Prelude

/-!
# digraph_is_subgraph_of

Topic: graphs   Node: ebd48f3f5c82

Provenance: formalization of a published result. Source: arXiv:2610.18600 Section 3

A directed graph G is a subgraph of H if there is an injective vertex map from V(G) to V(H) that sends every edge of G to an edge of H.
-/

/-- G is a subgraph of H if there is an injective map from V(G) to V(H) preserving directed edges. -/
def digraph_is_subgraph_of {V W : Type*} (G : Digraph V) (H : Digraph W) : Prop := ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)
