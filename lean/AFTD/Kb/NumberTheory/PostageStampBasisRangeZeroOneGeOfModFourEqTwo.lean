import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetLeOfForallLe
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumsetOfList
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_basis_range_zero_one_ge_of_mod_four_eq_two

Topic: elementary_number_theory   Node: ce6d09d81582

Provenance: formalization of a published result. Source: arXiv:2610.19470, Theorem 1.1 (Stöhr): for even h, {0, 1, (h+2)/2} is an extremal basis with n_h = [(h²+6h+1)/4]; this is its lower-bound half for h ≡ 2 (mod 4).

For h = 4w - 2 (w ≥ 1), the basis {0, 1, 2w} = {0, 1, (h+2)/2} has h-range at least (w+1)h = (h² + 6h)/4: every integer in [0, (w+1)h] is a sum of exactly h elements of {0, 1, 2w}.
-/

theorem postage_stamp_basis_range_zero_one_ge_of_mod_four_eq_two (w : ℕ) (hw : 1 ≤ w) :
    (w + 1) * (4 * w - 2) ≤ postage_stamp_basis_range (4 * w - 2) {0, 1, 2 * (w : ℤ)} := by
  apply le_csSup
  · refine ⟨(4 * w - 2) * (2 * w), fun n hn => ?_⟩
    have hn_in : int_mem_h_fold_sumset (4 * w - 2) {0, 1, 2 * (w : ℤ)} (n : ℤ) := hn n le_rfl
    have h_le := int_mem_h_fold_sumset_le_of_forall_le (4 * w - 2) {0, 1, 2 * (w : ℤ)} (2 * (w : ℤ)) (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> omega) (n : ℤ) hn_in
    exact_mod_cast h_le
  · intro m hm
    have h1 : 2 ≤ 4 * w := by omega
    have h2 : 2 ≤ 2 * w := by omega
    have h_bound : (w + 1) * (4 * w - 2) = 2 * w * (2 * w) + (2 * w - 2) := by
      zify [h1, h2]
      ring
    let q := m / (2 * w)
    let r := m % (2 * w)
    have h_div : 2 * w * q + r = m := Nat.div_add_mod m (2 * w)
    have hr : r < 2 * w := Nat.mod_lt m (by omega)
    have hm_le : 2 * w * q + r ≤ 2 * w * (2 * w) + (2 * w - 2) := by
      rw [h_div, ← h_bound]
      exact hm
    have hqr : q + r ≤ 4 * w - 2 := by
      have hm' : (2 * (w : ℤ) * (q : ℤ) + (r : ℤ) : ℤ) ≤ 2 * (w : ℤ) * (2 * (w : ℤ)) + (2 * (w : ℤ) - 2) := by
        zify [h2] at hm_le
        linarith
      have hr' : (r : ℤ) < 2 * (w : ℤ) := by exact_mod_cast hr
      have hw' : 1 ≤ (w : ℤ) := by exact_mod_cast hw
      have hq' : (q : ℤ) ≤ 2 * (w : ℤ) := by
        by_contra! h
        have : (2 * (w : ℤ) * (2 * (w : ℤ) + 1) : ℤ) ≤ 2 * (w : ℤ) * (q : ℤ) := by nlinarith
        nlinarith
      have hqr' : (q : ℤ) + (r : ℤ) ≤ 4 * (w : ℤ) - 2 := by
        by_cases hq_cases : (q : ℤ) ≤ 2 * (w : ℤ) - 1
        · linarith
        · have hq_eq : (q : ℤ) = 2 * (w : ℤ) := by linarith
          rw [hq_eq] at hm'
          linarith
      omega
    let l : List ℤ := List.replicate q (2 * (w : ℤ)) ++ List.replicate r 1 ++ List.replicate (4 * w - 2 - (q + r)) 0
    have hl_len : l.length = 4 * w - 2 := by
      dsimp [l]
      simp
      omega
    have hl_sum : l.sum = (m : ℤ) := by
      dsimp [l]
      simp
      linarith
    have hl_mem : ∀ x ∈ l, x ∈ ({0, 1, 2 * (w : ℤ)} : Finset ℤ) := by
      intro x hx
      dsimp [l] at hx
      simp only [List.mem_append, List.mem_replicate, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with (⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩ <;> tauto
    have h_ans := int_mem_h_fold_sumset_of_list {0, 1, 2 * (w : ℤ)} l hl_mem
    rw [hl_len, hl_sum] at h_ans
    exact h_ans
