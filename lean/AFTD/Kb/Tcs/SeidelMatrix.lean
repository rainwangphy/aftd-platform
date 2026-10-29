import AFTD.Prelude

/-!
# seidel_matrix

Topic: combinatorics   Node: c1e3c466c229

Provenance: formalization of a published result. Source: arXiv:2610.36522 Section 2; Seidel (1968)

The Seidel matrix of a simple graph G is the matrix S with zero on the diagonal, -1 for adjacent pairs of vertices, and 1 for distinct nonadjacent pairs of vertices.
-/

/-- The Seidel matrix of a simple graph with decidable adjacency. -/
def seidel_matrix {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℤ :=
  Matrix.of fun i j => if i = j then 0 else if G.Adj i j then -1 else 1
