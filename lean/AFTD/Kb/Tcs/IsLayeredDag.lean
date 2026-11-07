import AFTD.Prelude

/-!
# is_layered_dag

Topic: graphs   Node: 9c9fc10135a2

Provenance: formalization of a published result. Source: arXiv:2611.07043

A digraph G is a layered DAG with layer function layer : V → ℕ if every directed edge connects a vertex in layer i to a vertex in layer i + 1.
-/

/-- A digraph is a layered DAG if vertices have layer indices and every directed edge goes from a layer to the next layer. -/
def is_layered_dag {V : Type*} (G : Digraph V) (layer : V → ℕ) : Prop := ∀ u v, G.Adj u v → layer v = layer u + 1
