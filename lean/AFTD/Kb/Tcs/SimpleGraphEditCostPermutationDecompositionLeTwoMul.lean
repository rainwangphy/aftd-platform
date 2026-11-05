import AFTD.Prelude
import AFTD.Kb.Tcs.GraphEditCostPermutationDecompositionLeTwoMul
import AFTD.Kb.Tcs.PermEditCost
import AFTD.Kb.Tcs.GraphEditCost
import AFTD.Kb.Tcs.IsDoublyStochastic

/-!
# simple_graph_edit_cost_permutation_decomposition_le_two_mul

Topic: graphs   Node: 93c9e09b54f7

Provenance: helper lemma. arXiv:2611.05048 Theorem 6

For any simple graphs $G$ and $H$ on $n$ vertices and any doubly stochastic matrix $Q$ with a convex decomposition into permutation matrices $\sum_{i \in \iota} w_i P_{\pi_i}$, the weighted edit cost between the adjacency matrices satisfies $\sum_{i \in \iota} w_i \mathcal{C}_{\mathsf{ed}}(\pi_i) \le 2 \mathcal{C}_{\mathsf{ed}}(Q)$.
-/

/-- The factor-2 upper bound specialized to the adjacency matrices of simple graphs. -/
theorem simple_graph_edit_cost_permutation_decomposition_le_two_mul
    {n : ℕ} {ι : Type*} [Fintype ι]
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ_ds : is_doubly_stochastic Q)
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (π : ι → Equiv.Perm (Fin n))
    (hQ : ∑ i, w i • (π i).permMatrix ℝ = Q)
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    ∑ i, w i * perm_edit_cost (G.adjMatrix ℝ) (H.adjMatrix ℝ) (π i) ≤
      2 * graph_edit_cost (G.adjMatrix ℝ) (H.adjMatrix ℝ) Q := by
  apply graph_edit_cost_permutation_decomposition_le_two_mul Q hQ_ds w hw_nonneg hw_sum π hQ
  · intro i j
    simp only [SimpleGraph.adjMatrix, Matrix.of_apply]
    split_ifs <;> simp
  · intro i j
    simp only [SimpleGraph.adjMatrix, Matrix.of_apply]
    split_ifs <;> simp
