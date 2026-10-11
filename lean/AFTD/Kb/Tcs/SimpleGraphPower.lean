import AFTD.Prelude

/-!
# simple_graph_power

Topic: graphs   Node: 1e2cd8b5ef97

Provenance: formalization of a published result. Source: arXiv:2610.09300 (On graphs whose powers are well-covered), Sec. 1 and Sec. 2 (the d-th power G^d); the distance is Mathlib's extended distance edist, so vertices in different components are never adjacent.

The d-th power G^d of a graph G: same vertices, two distinct vertices adjacent iff they are joined by a path (equivalently a walk) of length at most d in G.
-/

/-- The `d`-th power of a graph: distinct vertices are adjacent when joined by a walk of length at most `d`. -/
def simple_graph_power {V : Type*} (G : SimpleGraph V) (d : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ G.edist u v ≤ d
  symm := ⟨fun u v (h : u ≠ v ∧ G.edist u v ≤ d) =>
    ⟨h.1.symm, by rw [SimpleGraph.edist_comm]; exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩
