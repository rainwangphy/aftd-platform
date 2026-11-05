import AFTD.Prelude
import AFTD.Kb.Tcs.GraphEditCost
import AFTD.Kb.Tcs.PermEditCost

/-!
# perm_edit_cost_eq_graph_edit_cost

Topic: graphs   Node: 386ca09ea007

Provenance: helper lemma. arXiv:2611.05048 Section 3, line 325

For any permutation $\pi$ of $\{0, \dots, n-1\}$ and matrices $A, B$, the permutation edit cost $\mathcal{C}_{\mathsf{ed}}(\pi)$ equals the fractional edit cost $\mathcal{C}_{\mathsf{ed}}(P_\pi)$ evaluated on the permutation matrix $P_\pi$.
-/

/-- The permutation edit cost equals the fractional edit cost on the permutation matrix. -/
theorem perm_edit_cost_eq_graph_edit_cost {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (π : Equiv.Perm (Fin n)) :
    perm_edit_cost A B π = graph_edit_cost A B (π.permMatrix ℝ) := by
  simp only [perm_edit_cost, graph_edit_cost]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro v' _
  have h1 : ∀ (i j : Fin n), (π.permMatrix ℝ) i j = if j = π i then 1 else 0 := by
    intro i j
    simp [Equiv.Perm.permMatrix, Equiv.toPEquiv, PEquiv.toMatrix, Matrix.of_apply, eq_comm]
  simp only [h1]
  rw [Finset.sum_eq_single (π v)]
  · rw [Finset.sum_eq_single (π v')]
    · simp
    · intro w' _ hw'
      simp [if_neg hw']
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro w _ hw
    simp [if_neg hw]
  · intro h
    exact absurd (Finset.mem_univ _) h
