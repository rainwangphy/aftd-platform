import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphDominatedBy

/-!
# simple_graph_is_dominated

Topic: graphs   Node: d0ecf3682b8f

Provenance: formalization of a published result. Source: arXiv:2611.14430, Section 2

A vertex in a simple graph is dominated if there exists another vertex dominating it.
-/

/-- A vertex is dominated if some distinct vertex dominates it. -/
def simple_graph_is_dominated {V : Type*} (G : SimpleGraph V) (u : V) : Prop :=
  ∃ t : V, simple_graph_dominated_by G u t
