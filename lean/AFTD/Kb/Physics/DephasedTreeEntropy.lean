import AFTD.Prelude
import AFTD.Kb.Physics.TreeSubmatrixKer
import AFTD.Kb.Physics.TreeSubmatrixDim
import AFTD.Kb.Physics.DephasedTreeProb

/-!
# dephased_tree_entropy

Topic: quantum_mechanics   Node: de43cac37d2e

Provenance: formalization of a published result. Source: Fuentes et al., arXiv:2511.19585; OP-827

For a finite simple graph T on vertex type V, noise profile q : V → ℝ, and subset S : Finset V, dephased_tree_entropy T q S is |S| - d_S - ∑_χ P_S(χ) log_2(P_S(χ)) with 0 log 0 = 0, where d_S = tree_submatrix_dim T S and P_S(χ) = dephased_tree_prob T q S χ.
-/

/-- Subsystem von Neumann entropy of an inhomogeneously dephased tree graph state. -/
noncomputable def dephased_tree_entropy {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (q : V → ℝ) (S : Finset V) : ℝ := open scoped Classical BigOperators in
  (S.card : ℝ) - (tree_submatrix_dim T S : ℝ) -
    ∑ χ : AddChar (tree_submatrix_ker T S) ℝ,
      let p := dephased_tree_prob T q S χ
      if p = 0 then 0 else p * Real.logb 2 p
