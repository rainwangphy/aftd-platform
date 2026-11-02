import AFTD.Prelude
import AFTD.Kb.Physics.TreeSubmatrixKer
import AFTD.Kb.Physics.TreeSubmatrixDim

/-!
# dephased_tree_prob

Topic: quantum_mechanics   Node: e410fce31931

Provenance: formalization of a published result. Source: Fuentes et al., arXiv:2511.19585; OP-827

For a finite simple graph T on vertex type V, a noise parameter function q : V → ℝ, a subset S : Finset V, and an additive character χ : AddChar (tree_submatrix_ker T S) ℝ, dephased_tree_prob T q S χ is 2^(-d_S) * ∑_{x ∈ K_S} χ(x) * ∏_{i ∈ S, x_i = 1} q(i), where d_S = tree_submatrix_dim T S.
-/

/-- Probability of character chi under local Z noise on tree graph state subsystem S. -/
noncomputable def dephased_tree_prob {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (q : V → ℝ) (S : Finset V)
    (χ : AddChar (tree_submatrix_ker T S) ℝ) : ℝ := open scoped Classical BigOperators in
  (1 / 2 : ℝ) ^ (tree_submatrix_dim T S) *
    ∑ x : tree_submatrix_ker T S,
      χ x * ∏ i ∈ Finset.univ.filter (fun (i : ↥S) => x.1 i = 1), q (i : V)
