import AFTD.Prelude
import AFTD.Kb.Tcs.MonoColorSubgraph

/-!
# is_monochromatic_path

Topic: graphs   Node: f01e3a2490e7

Provenance: formalization of a published result. Source: arXiv:2611.06362 Section 1

A finite set of vertices s in a simple graph G with edge colouring c : G.edgeSet → C is the vertex set of a monochromatic path if there exist a colour col : C, vertices u v : V, and a simple path p in the monochromatic subgraph mono_color_subgraph G c col from u to v such that s = p.support.toFinset.
-/

/-- Predicate asserting that a finite set of vertices spans a monochromatic path in an edge-coloured simple graph. -/
def is_monochromatic_path {V C : Type*} [DecidableEq V] (G : SimpleGraph V) (c : G.edgeSet → C)
    (s : Finset V) : Prop :=
  ∃ (col : C) (u v : V) (p : (mono_color_subgraph G c col).Walk u v),
    p.IsPath ∧ s = p.support.toFinset
