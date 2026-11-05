import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLaplacianMatrix
import AFTD.Kb.Tcs.SimpleGraphLaplacianMatrixIsHermitian

/-!
# simple_graph_laplacian_second_eigenvalue

Topic: graphs   Node: 5389eb7672bf

Provenance: formalization of a published result. Source: arXiv:2611.03879, Section 1

Given a finite type V with decidable equality and a simple graph G on V with decidable adjacency, simple_graph_laplacian_second_eigenvalue is defined as (simple_graph_laplacian_matrix_isHermitian G).eigenvalues₀ evaluated at ⟨1, h⟩ if 2 ≤ Fintype.card V, and 0 otherwise.
-/

/-- The second largest eigenvalue μ₂ of the Laplacian matrix of a finite simple graph. -/
noncomputable def simple_graph_laplacian_second_eigenvalue {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ := if h : 2 ≤ Fintype.card V then
    (simple_graph_laplacian_matrix_isHermitian G).eigenvalues₀ ⟨1, h⟩
  else 0
