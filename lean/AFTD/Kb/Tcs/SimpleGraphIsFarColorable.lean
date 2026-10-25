import AFTD.Prelude

/-!
# simple_graph_is_far_colorable

Topic: combinatorics   Node: 11a38bee5768

Provenance: formalization of a published result. Source: combinatorics/2610-31489-near-optimal-bounds-for-testing-k-colorability.md:126

A finite simple graph G on vertex type V is ε-far from being k-colorable if for every edge subset E' ⊆ E(G), whenever deleting E' from G leaves a k-colorable graph, the cardinality of E' is at least ε |V|².
-/

/-- A finite simple graph G is ε-far from being k-colorable if at least ε |V|² edges must be deleted from G to make it k-colorable. -/
def simple_graph_is_far_colorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (ε : ℝ) : Prop := ∀ E' ⊆ G.edgeFinset, (G.deleteEdges (E' : Set (Sym2 V))).Colorable k →
    ε * (Fintype.card V : ℝ) ^ 2 ≤ (E'.card : ℝ)
