import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetLeOfForallLe
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetOfList
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_basis_range_zero_one_ge_of_mod_four_eq_zero

Topic: elementary_number_theory   Node: 95c5f12d1bb2

Provenance: formalization of a published result. Source: arXiv:2610.19470, Theorem 1.1 (Stöhr): for even h, {0, 1, (h+2)/2} is an extremal basis with n_h = [(h²+6h+1)/4]; this is its lower-bound half for h ≡ 0 (mod 4).

For h = 4w (w ≥ 1), the basis {0, 1, 2w + 1} = {0, 1, (h+2)/2} has h-range at least w(4w + 6) = (h² + 6h)/4: every integer in [0, w(4w+6)] is a sum of exactly h elements of {0, 1, 2w + 1}.
-/

theorem postage_stamp_basis_range_zero_one_ge_of_mod_four_eq_zero (w : ℕ) (hw : 1 ≤ w) :
    w * (4 * w + 6) ≤ postage_stamp_basis_range (4 * w) {0, 1, 2 * (w : ℤ) + 1} := by
  apply le_csSup
  · refine ⟨4 * w * (2 * w + 1), fun n hn => ?_⟩
    have hn_in : int_mem_h_fold_sumset (4 * w) {0, 1, 2 * (w : ℤ) + 1} (n : ℤ) := hn n le_rfl
    have h_le := int_mem_h_fold_sumset_le_of_forall_le (4 * w) {0, 1, 2 * (w : ℤ) + 1} (2 * (w : ℤ) + 1) (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> omega) (n : ℤ) hn_in
    exact_mod_cast h_le
  · intro m hm
    let q := m / (2 * w + 1)
    let r := m % (2 * w + 1)
    have h_div : (2 * w + 1) * q + r = m := Nat.div_add_mod m (2 * w + 1)
    have hr : r < 2 * w + 1 := Nat.mod_lt m (by omega)
    have h_bound : w * (4 * w + 6) = (2 * w + 1) * (2 * w + 1) + (2 * w - 1) := by
      have h1 : 1 ≤ 2 * w := by omega
      zify [h1]
      ring
    have hm_le : (2 * w + 1) * q + r ≤ (2 * w + 1) * (2 * w + 1) + (2 * w - 1) := by
      calc
        (2 * w + 1) * q + r = m := h_div
        _ ≤ w * (4 * w + 6) := hm
        _ = (2 * w + 1) * (2 * w + 1) + (2 * w - 1) := h_bound
    have hqr : q + r ≤ 4 * w := by
      by_cases hq : q ≤ 2 * w
      · omega
      · have hq_ge : 2 * w + 1 ≤ q := by omega
        have hq_le : q ≤ 2 * w + 1 := by
          by_contra! h
          have : 2 * w + 2 ≤ q := h
          have h1 : (2 * w + 1) * (2 * w + 2) ≤ (2 * w + 1) * q := Nat.mul_le_mul_left _ this
          have h2 : (2 * w + 1) * (2 * w + 1) + (2 * w - 1) < (2 * w + 1) * (2 * w + 2) := by
            have : 1 ≤ 2 * w := by omega
            zify [this]
            ring_nf
            linarith
          omega
        have hq_eq : q = 2 * w + 1 := by omega
        have hr_le : r ≤ 2 * w - 1 := by
          have : (2 * w + 1) * (2 * w + 1) + r ≤ (2 * w + 1) * (2 * w + 1) + (2 * w - 1) := by
            calc (2 * w + 1) * (2 * w + 1) + r = (2 * w + 1) * q + r := by rw [hq_eq]
            _ ≤ (2 * w + 1) * (2 * w + 1) + (2 * w - 1) := hm_le
          exact Nat.le_of_add_le_add_left this
        omega
    let l : List ℤ := List.replicate q (2 * (w : ℤ) + 1) ++ List.replicate r 1 ++ List.replicate (4 * w - (q + r)) 0
    have hl_len : l.length = 4 * w := by
      dsimp [l]
      simp
      omega
    have hl_sum : l.sum = (m : ℤ) := by
      dsimp [l]
      simp
      have : ((2 * w + 1) * q + r : ℤ) = (m : ℤ) := by exact_mod_cast h_div
      linarith
    have hl_mem : ∀ x ∈ l, x ∈ ({0, 1, 2 * (w : ℤ) + 1} : Finset ℤ) := by
      intro x hx
      dsimp [l] at hx
      simp only [List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with (⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩ <;> tauto
    have h_ans := int_mem_h_fold_sumset_of_list {0, 1, 2 * (w : ℤ) + 1} l hl_mem
    rw [hl_len, hl_sum] at h_ans
    exact h_ans
