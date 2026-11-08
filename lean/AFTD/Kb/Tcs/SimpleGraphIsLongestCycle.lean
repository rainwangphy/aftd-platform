import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsCycleSubgraph

/-!
# simple_graph_is_longest_cycle

Topic: graphs   Node: 0f380bec09f0

Provenance: formalization of a published result. Source: arXiv:2611.07145 Sec. 1

A subgraph C of a simple graph G is a longest cycle if it is a cycle subgraph and its vertex set has maximum cardinality among all cycle subgraphs of G.
-/

/-- A cycle subgraph C is a longest cycle in G if its vertex set has maximal cardinality among all cycle subgraphs. -/
def simple_graph_is_longest_cycle {V : Type*} {G : SimpleGraph V} (C : G.Subgraph) : Prop := simple_graph_is_cycle_subgraph C ∧ ∀ C' : G.Subgraph, simple_graph_is_cycle_subgraph C' → C'.verts.ncard ≤ C.verts.ncard
