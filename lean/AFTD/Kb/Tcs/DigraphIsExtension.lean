import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsOriented

/-!
# digraph_is_extension

Topic: graphs   Node: 39c192db8025

Provenance: formalization of a published result. Source: arXiv:2611.32872 p. 3

A directed graph H is an extension of a directed graph G if H is oriented and G is a subgraph of H.
-/

/-- A digraph H is an extension of G if H is an oriented supergraph of G. -/
def digraph_is_extension {V : Type*} (G H : Digraph V) : Prop := digraph_is_oriented H ∧ G ≤ H
