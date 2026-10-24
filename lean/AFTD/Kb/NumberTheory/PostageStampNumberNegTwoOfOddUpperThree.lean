import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddCasesTwo
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddBounds
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddRangeLt
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddDecomp
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumset

/-!
# postage_stamp_number_neg_two_of_odd_upper_three

Topic: elementary_number_theory   Node: 2f204b32ebd2

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

For odd h ≥ 5 with h ≡ 11 (mod 12), every 3-element set with a negative element has h-range at most n_h(2) - 3.
-/

theorem postage_stamp_number_neg_two_of_odd_upper_three (h : ℕ) (hh : 5 ≤ h) (ho : h % 2 = 1)
    (h11 : h % 12 = 11) (A : Finset ℤ) (hA : A.card = 3) (hneg : ∃ a ∈ A, a < 0) :
    postage_stamp_basis_range h A + 3 ≤ (h ^ 2 + 6 * h + 1) / 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, h = 2*m+1 := Nat.odd_iff.mpr ho
  have hm : 5 ≤ m := by omega
  have hm6 : m % 6 = 5 := by omega
  have hN : ((2*m+1 : ℕ)^2 + 6*(2*m+1) + 1)/4 = m^2 + 4*m + 2 := by
    have h : (2*m+1 : ℕ)^2 + 6*(2*m+1) + 1 = 4*(m^2+4*m+2) := by ring
    rw [h]
    exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)
  rw [hN]
  obtain ⟨a, x, y, hx, hxy, ha, hAeq⟩ :=
    postage_stamp_number_neg_two_of_odd_decomp A hA hneg
  have hR : 2*m+1+1 ≤ m^2+4*m := by nlinarith
  have key : ¬ ∀ n : ℕ, n ≤ m^2 + 4*m → int_mem_h_fold_sumset (2*m+1) A n := by
    intro hsub
    rw [hAeq] at hsub
    obtain ⟨hcop, haU, haL⟩ :=
      postage_stamp_number_neg_two_of_odd_bounds m (m^2+4*m) hR a x y hx hxy ha hsub
    exact postage_stamp_number_neg_two_of_odd_cases_two m hm hm6 a x y hx hxy ha hcop haU haL
  have := postage_stamp_number_neg_two_of_odd_range_lt (2*m+1) (m^2+4*m) A (by omega) key
  omega
