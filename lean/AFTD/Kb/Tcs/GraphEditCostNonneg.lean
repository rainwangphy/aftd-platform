import AFTD.Prelude
import AFTD.Kb.Tcs.GraphEditCost

/-!
# graph_edit_cost_nonneg

Topic: graphs   Node: ee06be578271

Provenance: helper lemma. arXiv:2611.05048 Section 2

For any $n \times n$ real matrices $A$ and $B$ and any matrix $Q$ with non-negative entries, the edit cost $\mathcal{C}_{\mathsf{ed}}(Q)$ is non-negative.
-/

/-- The edit cost of a fractional alignment with non-negative entries is non-negative. -/
theorem graph_edit_cost_nonneg {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) :
    0 ≤ graph_edit_cost A B Q := by
  unfold graph_edit_cost
  refine Finset.sum_nonneg (fun v _ => Finset.sum_nonneg (fun v' _ =>
    Finset.sum_nonneg (fun w _ => Finset.sum_nonneg (fun w' _ => ?_))))
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (hQ v w)) (hQ v' w')
