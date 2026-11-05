import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLaplacianMatrix
import AFTD.Kb.Tcs.IsTreeInduceComplSingleton

/-!
# simple_graph_laplacian_matrix_isHermitian

Topic: graphs   Node: 80c320499581

Provenance: formalization of a published result. Source: arXiv:2611.03879, Section 1

The Laplacian matrix of any finite simple graph is Hermitian.
-/

/-- The Laplacian matrix of a finite simple graph is Hermitian (real symmetric). -/
lemma simple_graph_laplacian_matrix_isHermitian {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (simple_graph_laplacian_matrix G).IsHermitian := by first | exact is_tree_induce_compl_singleton | (apply is_tree_induce_compl_singleton <;> assumption) | (apply is_tree_induce_compl_singleton <;> simp_all) | simpa using is_tree_induce_compl_singleton | (simp only [simple_graph_laplacian_matrix] at *; first | exact is_tree_induce_compl_singleton | (apply is_tree_induce_compl_singleton <;> assumption) | (apply is_tree_induce_compl_singleton <;> simp_all) | simpa using is_tree_induce_compl_singleton)
