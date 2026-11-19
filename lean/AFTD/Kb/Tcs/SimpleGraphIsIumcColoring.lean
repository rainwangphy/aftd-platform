import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_is_iumc_coloring

Topic: graphs   Node: 48afa7ee16b3

Provenance: formalization of a published result. Source: arXiv:2611.23478, Section 1

A vertex colouring of a graph G is an iUMc-colouring (unique-maximum colouring with respect to closed neighbourhoods) if, for every vertex v, the maximum colour in the closed neighbourhood N[v] is attained by exactly one vertex.
-/

/-- A colouring of the vertices of a graph is an iUMc-colouring if in the closed neighbourhood of every vertex, the maximum colour appears on exactly one vertex. -/
def simple_graph_is_iumc_coloring {V α : Type*} [LinearOrder α] (G : SimpleGraph V) (c : V → α) : Prop := ∀ v : V, ∃ u ∈ insert v (G.neighborSet v), ∀ w ∈ insert v (G.neighborSet v), w ≠ u → c w < c u
