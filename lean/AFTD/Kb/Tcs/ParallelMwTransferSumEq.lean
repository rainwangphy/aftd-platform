import AFTD.Prelude
import AFTD.Kb.Tcs.ParallelMwTransfer

/-!
# parallel_mw_transfer_sum_eq

Topic: combinatorics   Node: dc49f74aceb3

Provenance: helper lemma. folklore

For any natural number n, any function q : Fin n → ℕ, and any indices i, j : Fin n with i ≠ j and 1 ≤ q j, the sum of parallel_mw_transfer q i j k over all k : Fin n equals the sum of q k over all k : Fin n.
-/

/-- A transfer between distinct indices preserves the sum of parallel-class sizes. -/
theorem parallel_mw_transfer_sum_eq {n : ℕ} (q : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (hj : 1 ≤ q j) :
    ∑ k : Fin n, parallel_mw_transfer q i j k = ∑ k : Fin n, q k := by
  dsimp [parallel_mw_transfer]
  rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
  have hi : i ∈ Finset.univ \ {j} := by simp [hij]
  rw [Finset.sum_update_of_mem hi]
  conv_rhs =>
    rw [← Function.update_eq_self j q]
    rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
    right
    rw [← Function.update_eq_self i q]
    rw [Finset.sum_update_of_mem hi]
  omega
