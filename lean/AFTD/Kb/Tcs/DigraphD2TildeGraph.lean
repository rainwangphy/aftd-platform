import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphD2TildeVertex
import AFTD.Kb.Tcs.DigraphD2TildeAdjBool

/-!
# digraph_d2_tilde_graph

Topic: combinatorics   Node: 7f3585478a25

Provenance: formalization of a published result. Source: arXiv:2611.15027 Section 5

The underlying simple graph of the directed graph D̃₂, defined on DigraphD2TildeVertex as SimpleGraph.fromRel (fun a b => digraph_d2_tilde_adj_bool a b = true).
-/

/-- The underlying simple graph of the directed graph D̃₂. -/
def digraph_d2_tilde_graph : SimpleGraph DigraphD2TildeVertex := SimpleGraph.fromRel (fun a b => digraph_d2_tilde_adj_bool a b = true)
