import AFTD.Prelude

/-!
# closed_neighborhood

Topic: combinatorial_games   Node: a4953c0c5ff0

Provenance: formalization of a published result. Source: arXiv:2611.01281 Section 2

Given a finite type V with decidable equality, a simple graph G on V with decidable adjacency, and a finite subset A : Finset V, `closed_neighborhood G A` is the finite set of vertices v : Finset V for which there exists some u ∈ A such that u = v or G.Adj u v.
-/

/-- The closed one-step neighborhood of a set of vertices in a simple graph. -/
def closed_neighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset V :=
  Finset.univ.filter fun v => ∃ u ∈ A, u = v ∨ G.Adj u v
