import AFTD.Prelude

/-!
# simple_graph_is_cycle_subgraph

Topic: graphs   Node: 485247419bea

Provenance: formalization of a published result. Source: arXiv:2611.07145 Sec. 2

A subgraph C of a simple graph G is a cycle if C is the subgraph traversed by a cycle walk in G.
-/

/-- A subgraph C of a simple graph G is a cycle if it is the subgraph of a cycle walk. -/
def simple_graph_is_cycle_subgraph {V : Type*} {G : SimpleGraph V} (C : G.Subgraph) : Prop := ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.toSubgraph = C
