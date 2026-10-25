import AFTD.Prelude

/-!
# simple_graph_pendant_triple_expand

Topic: graphs   Node: 3b5a96efae36

Provenance: helper lemma. Helper construction for the local palette reduction for OP-309, related to arXiv:2610.21868, Conjecture 1.1. Defined for any u,v; coloring extension assumes uv is an edge.

Replace uv by the path u-0-1-2-v on three fresh internal vertices, with fresh pendant leaves 3,4,5 at 0,1,2. Other original edges remain embedded into V plus Fin 6.
-/

def simple_graph_pendant_triple_expand {V : Type*} (G : SimpleGraph V)
    (u v : V) : SimpleGraph (V ⊕ Fin 6) :=
  (G.deleteEdges {s(u,v)}).map (Function.Embedding.inl : V ↪ V ⊕ Fin 6) ⊔
    SimpleGraph.fromEdgeSet {
      s(Sum.inl u, Sum.inr 0), s(Sum.inr 0, Sum.inr 1),
      s(Sum.inr 1, Sum.inr 2), s(Sum.inr 2, Sum.inl v),
      s(Sum.inr 0, Sum.inr 3), s(Sum.inr 1, Sum.inr 4),
      s(Sum.inr 2, Sum.inr 5)}
