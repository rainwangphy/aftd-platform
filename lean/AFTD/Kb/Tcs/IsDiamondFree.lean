import AFTD.Prelude
import AFTD.Kb.Tcs.DiamondGraph

/-!
# is_diamond_free

Topic: graphs   Node: 569394ba7362

Provenance: formalization of a published result. Source: arXiv:2610.32404:131

A simple graph G is diamond-free if it does not contain the diamond graph as an induced subgraph.
-/

/-- A simple graph is diamond-free if it contains no induced subgraph isomorphic to the diamond graph. -/
def is_diamond_free {V : Type*} (G : SimpleGraph V) : Prop := ¬ SimpleGraph.IsIndContained diamond_graph G
