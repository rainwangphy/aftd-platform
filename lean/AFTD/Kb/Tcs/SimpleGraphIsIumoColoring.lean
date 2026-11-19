import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_is_iumo_coloring

Topic: graphs   Node: efb5aed4bc37

Provenance: formalization of a published result. Source: arXiv:2611.23478, Section 1

A vertex colouring of a graph G is an iUMo-colouring (unique-maximum colouring with respect to open neighbourhoods) if, for every vertex v, the maximum colour in the open neighbourhood N(v) is attained by exactly one vertex.
-/

/-- A colouring of the vertices of a graph is an iUMo-colouring if in the open neighbourhood of every vertex, the maximum colour appears on exactly one vertex. -/
def simple_graph_is_iumo_coloring {V α : Type*} [LinearOrder α] (G : SimpleGraph V) (c : V → α) : Prop := ∀ v : V, ∃ u ∈ G.neighborSet v, ∀ w ∈ G.neighborSet v, w ≠ u → c w < c u
