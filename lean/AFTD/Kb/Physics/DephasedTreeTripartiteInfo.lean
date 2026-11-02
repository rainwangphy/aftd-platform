import AFTD.Prelude
import AFTD.Kb.Physics.DephasedTreeEntropy

/-!
# dephased_tree_tripartite_info

Topic: quantum_mechanics   Node: f89be2913edc

Provenance: formalization of a published result. Source: Fuentes et al., arXiv:2511.19585; OP-827

For a finite simple graph T on vertex type V, noise profile q : V → ℝ, and subsets A, B, C : Finset V, dephased_tree_tripartite_info T q A B C is H(A) + H(B) + H(C) - H(A ∪ B) - H(A ∪ C) - H(B ∪ C) + H(A ∪ B ∪ C), where H = dephased_tree_entropy T q.
-/

/-- Tripartite information of three disjoint subsystems for a dephased tree graph state. -/
noncomputable def dephased_tree_tripartite_info {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (q : V → ℝ) (A B C : Finset V) : ℝ := dephased_tree_entropy T q A +
  dephased_tree_entropy T q B +
  dephased_tree_entropy T q C -
  dephased_tree_entropy T q (A ∪ B) -
  dephased_tree_entropy T q (A ∪ C) -
  dephased_tree_entropy T q (B ∪ C) +
  dephased_tree_entropy T q (A ∪ B ∪ C)
