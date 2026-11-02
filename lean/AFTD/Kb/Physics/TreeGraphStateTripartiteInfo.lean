import AFTD.Prelude
import AFTD.Kb.Physics.SimpleGraphCutRank

/-!
# tree_graph_state_tripartite_info

Topic: quantum_mechanics   Node: 40cf7f107d8d

Provenance: formalization of a published result. Source: arXiv:2511.19585 Eq. (2.5)

For a simple graph G on a finite type V with decidable equality and decidable adjacency, and four finite subsets A, B, C, D : Finset V, tree_graph_state_tripartite_info G A B C D is the integer (simple_graph_cut_rank G A : ℤ) + (simple_graph_cut_rank G B : ℤ) + (simple_graph_cut_rank G C : ℤ) + (simple_graph_cut_rank G D : ℤ) - (simple_graph_cut_rank G (A ∪ B) : ℤ) - (simple_graph_cut_rank G (A ∪ C) : ℤ) - (simple_graph_cut_rank G (B ∪ C) : ℤ).
-/

/-- Tripartite information I₃(A:B:C) of a 4-partition (A, B, C, D) of a graph state, defined via cut ranks over F₂. -/
noncomputable def tree_graph_state_tripartite_info {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B C D : Finset V) : ℤ := (simple_graph_cut_rank G A : ℤ) + (simple_graph_cut_rank G B : ℤ) +
  (simple_graph_cut_rank G C : ℤ) + (simple_graph_cut_rank G D : ℤ) -
  (simple_graph_cut_rank G (A ∪ B) : ℤ) -
  (simple_graph_cut_rank G (A ∪ C) : ℤ) -
  (simple_graph_cut_rank G (B ∪ C) : ℤ)
