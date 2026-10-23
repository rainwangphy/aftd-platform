import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetLeOfForallLe
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetOfList
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_basis_range_zero_one_ge_of_odd

Topic: elementary_number_theory   Node: d95f67d1ea08

Provenance: formalization of a published result. Source: arXiv:2610.19470, Theorem 1.1 (Stöhr): for odd h, {0, 1, (h+3)/2} is the extremal basis with n_h = (h²+6h+1)/4; this is its lower-bound half. Checked for odd h ≤ 29 (experiment 3525).

For odd h = 2m + 1, Stöhr's extremal basis {0, 1, (h+3)/2} = {0, 1, m+2} has h-range at least m² + 4m + 2 = (h² + 6h + 1)/4: every integer in [0, m²+4m+2] is a sum of exactly h elements of {0, 1, m+2}.
-/

theorem postage_stamp_basis_range_zero_one_ge_of_odd (m : ℕ) :
    m ^ 2 + 4 * m + 2 ≤ postage_stamp_basis_range (2 * m + 1) {0, 1, (m : ℤ) + 2} := by
  apply le_csSup
  · refine ⟨(2 * m + 1) * (m + 2), fun n hn => ?_⟩
    have hn_in : int_mem_h_fold_sumset (2 * m + 1) {0, 1, (m : ℤ) + 2} (n : ℤ) := hn n le_rfl
    have h_le := int_mem_h_fold_sumset_le_of_forall_le (2 * m + 1) {0, 1, (m : ℤ) + 2} ((m : ℤ) + 2) (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> omega) (n : ℤ) hn_in
    exact_mod_cast h_le
  · intro k hk
    let q := k / (m + 2)
    let r := k % (m + 2)
    have h_div : (m + 2) * q + r = k := Nat.div_add_mod k (m + 2)
    have hr : r < m + 2 := Nat.mod_lt k (by omega)
    have hk_le : (m + 2) * q + r ≤ m ^ 2 + 4 * m + 2 := by
      rw [h_div]
      exact hk
    have hqr : q + r ≤ 2 * m + 1 := by
      nlinarith
    let l : List ℤ := List.replicate q ((m : ℤ) + 2) ++ List.replicate r 1 ++ List.replicate (2 * m + 1 - (q + r)) 0
    have hl_len : l.length = 2 * m + 1 := by
      dsimp [l]
      simp
      omega
    have hl_sum : l.sum = (k : ℤ) := by
      dsimp [l]
      simp
      have : ((m + 2) * q + r : ℤ) = (k : ℤ) := by exact_mod_cast h_div
      linarith
    have hl_mem : ∀ x ∈ l, x ∈ ({0, 1, (m : ℤ) + 2} : Finset ℤ) := by
      intro x hx
      dsimp [l] at hx
      simp only [List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with (⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩ <;> tauto
    have h_ans := int_mem_h_fold_sumset_of_list {0, 1, (m : ℤ) + 2} l hl_mem
    rw [hl_len, hl_sum] at h_ans
    exact h_ans
