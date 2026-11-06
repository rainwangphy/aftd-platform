import AFTD.Prelude

/-!
# simple_graph_is_nut_graph

Topic: graphs   Node: c9bc35bdc2a6

Provenance: formalization of a published result. Source: arXiv:2611.08244 Section 4

A finite simple graph G is a nut graph if its adjacency matrix over ℝ has nullity 1 and every non-zero vector in the null space has a non-zero entry at each vertex.
-/

/-- A simple graph G is a nut graph if the null space of its real adjacency matrix is 1-dimensional and contains no non-zero vector with a zero entry. -/
def simple_graph_is_nut_graph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop := Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ))) = 1 ∧
    ∀ x ∈ LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ)), x ≠ 0 → ∀ v : V, x v ≠ 0
