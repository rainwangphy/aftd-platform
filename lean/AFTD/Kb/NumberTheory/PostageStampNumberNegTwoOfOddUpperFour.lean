import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddCasesThree
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddBounds
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddRangeLt
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddDecomp
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumset

/-!
# postage_stamp_number_neg_two_of_odd_upper_four

Topic: elementary_number_theory   Node: d72d7a8a86cb

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

For odd h ≥ 5 with h ≡ 59 (mod 60), every 3-element set with a negative element has h-range at most n_h(2) - 4.
-/

theorem postage_stamp_number_neg_two_of_odd_upper_four (h : ℕ) (hh : 5 ≤ h) (ho : h % 2 = 1)
    (h59 : h % 60 = 59) (A : Finset ℤ) (hA : A.card = 3) (hneg : ∃ a ∈ A, a < 0) :
    postage_stamp_basis_range h A + 4 ≤ (h ^ 2 + 6 * h + 1) / 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, h = 2*m+1 := Nat.odd_iff.mpr ho
  have hm30 : m % 30 = 29 := by omega
  have hm : 29 ≤ m := by omega
  have hN : ((2*m+1 : ℕ)^2 + 6*(2*m+1) + 1)/4 = m^2 + 4*m + 2 := by
    have h : (2*m+1 : ℕ)^2 + 6*(2*m+1) + 1 = 4*(m^2+4*m+2) := by ring
    rw [h]
    exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)
  rw [hN]
  obtain ⟨a, x, y, hx, hxy, ha, hAeq⟩ :=
    postage_stamp_number_neg_two_of_odd_decomp A hA hneg
  have h1 : 1 ≤ m^2+4*m := by nlinarith
  have hR : 2*m+1+1 ≤ m^2+4*m-1 := by
    have : 2*m+1+1+1 ≤ m^2+4*m := by nlinarith
    omega
  have key : ¬ ∀ n : ℕ, n ≤ m^2 + 4*m - 1 → int_mem_h_fold_sumset (2*m+1) A n := by
    intro hsub
    rw [hAeq] at hsub
    obtain ⟨hcop, haU, haL⟩ :=
      postage_stamp_number_neg_two_of_odd_bounds m (m^2+4*m-1) hR a x y hx hxy ha hsub
    have hc : ((m^2+4*m-1 : ℕ) : ℤ) = (m:ℤ)^2 + 4*(m:ℤ) - 1 := by
      rw [Nat.cast_sub h1]; push_cast; ring
    rw [hc] at haL
    exact postage_stamp_number_neg_two_of_odd_cases_three m hm30 a x y hx hxy ha hcop haU haL
  have := postage_stamp_number_neg_two_of_odd_range_lt (2*m+1) (m^2+4*m-1) A (by omega) key
  omega
