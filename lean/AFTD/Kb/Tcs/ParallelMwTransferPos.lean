import AFTD.Prelude
import AFTD.Kb.Tcs.ParallelMwTransfer

/-!
# parallel_mw_transfer_pos

Topic: combinatorics   Node: ff1ffcf998fd

Provenance: helper lemma. folklore

For any natural number n, any function q : Fin n → ℕ such that 0 < q k for all k : Fin n, and any indices i, j : Fin n with q i + 2 ≤ q j, 0 < parallel_mw_transfer q i j k for every k : Fin n.
-/

/-- A transfer between classes with q_j ≥ q_i + 2 preserves positivity of all entries. -/
theorem parallel_mw_transfer_pos {n : ℕ} (q : Fin n → ℕ) (hq : ∀ k, 0 < q k)
    (i j : Fin n) (hij : q i + 2 ≤ q j) (k : Fin n) :
    0 < parallel_mw_transfer q i j k := by
  dsimp [parallel_mw_transfer]
  by_cases hkj : k = j
  · subst hkj
    rw [Function.update_self]
    omega
  · rw [Function.update_of_ne hkj]
    by_cases hki : k = i
    · subst hki
      rw [Function.update_self]
      omega
    · rw [Function.update_of_ne hki]
      exact hq k
