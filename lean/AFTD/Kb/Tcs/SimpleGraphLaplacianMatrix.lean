import AFTD.Prelude

/-!
# simple_graph_laplacian_matrix

Topic: graphs   Node: b928ef92edcd

Provenance: formalization of a published result. Source: arXiv:2611.03879, Section 1

The Laplacian matrix of a finite simple graph G is the diagonal degree matrix minus the real adjacency matrix of G.
-/

/-- The Laplacian matrix L = D - A of a finite simple graph G over ℝ. -/
def simple_graph_laplacian_matrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ := Matrix.diagonal (fun v => (G.degree v : ℝ)) - G.adjMatrix ℝ
