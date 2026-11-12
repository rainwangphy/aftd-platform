import AFTD.Prelude

/-!
# simple_graph_is_cone

Topic: graphs   Node: 73f084dd7230

Provenance: formalization of a published result. Source: arXiv:2611.14430, Section 2

A simple graph is a cone if it is non-empty and has an apex (a universal vertex adjacent to all other vertices).
-/

/-- A simple graph is a cone if it is non-empty and has a universal vertex (apex). -/
def simple_graph_is_cone {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty V ∧ ∃ apex : V, G.IsUniversal apex
