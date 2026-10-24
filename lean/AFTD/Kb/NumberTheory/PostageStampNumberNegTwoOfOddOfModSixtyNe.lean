import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.PostageStampBasisRangeAddOneLeOfNegOfOdd
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddFamilyE
import AFTD.Kb.NumberTheory.PostageStampBasisRangeAddTwoLeOfNegOfOdd
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddSandwich
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddRangeGe
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddUpperThree
import AFTD.Kb.NumberTheory.PostageStampNumberNeg
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.NumberTheory.PostageStampBasisRangeNegGeOfModTwelveEqNine
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddFamily2
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddFamily1

/-!
# postage_stamp_number_neg_two_of_odd_of_mod_sixty_ne

Topic: elementary_number_theory   Node: fe666bf6ad1e

Provenance: original. Related work: arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 (n♭_h(2) < n_h(2) for odd h)

Exact value of the negative-allowed three-stamp number for odd h ≥ 5 with h ≢ 59 (mod 60): n_h(2) - n♭_h(2) = 1 if h ≡ 9 (mod 12), 2 if h ≡ 1, 3, 5, 7 (mod 12), and 3 if h ≡ 11 (mod 12); here n_h(2) = ⌊(h²+6h+1)/4⌋.
-/

theorem postage_stamp_number_neg_two_of_odd_of_mod_sixty_ne (h : ℕ) (hh : 5 ≤ h) (ho : h % 2 = 1)
    (h60 : h % 60 ≠ 59) :
    postage_stamp_number_neg h 2 + (if h % 12 = 9 then 1 else if h % 12 ≠ 11 then 2 else 3) =
      (h ^ 2 + 6 * h + 1) / 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, h = 2*m+1 := Nat.odd_iff.mpr ho
  have hN : ((2*m+1 : ℕ)^2 + 6*(2*m+1) + 1)/4 = m^2 + 4*m + 2 := by
    have h : (2*m+1 : ℕ)^2 + 6*(2*m+1) + 1 = 4*(m^2+4*m+2) := by ring
    rw [h]
    exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)
  have hm : 2 ≤ m := by omega
  have hmZ : (2:ℤ) ≤ m := by exact_mod_cast hm
  split_ifs with h9 h11
  · obtain ⟨r, hr⟩ : ∃ r, m = 6 * r + 4 := ⟨m / 6, by omega⟩
    have hh' : 2 * m + 1 = 12 * r + 9 := by omega
    rw [hh']
    have hcard : ({-(2 * (r : ℤ) + 2), 2 * (r : ℤ) + 2, 4 * (r : ℤ) + 5} : Finset ℤ).card = 3 := by
      have : (0 : ℤ) ≤ r := Nat.cast_nonneg r
      rw [Finset.card_eq_three]
      exact ⟨_, _, _, by omega, by omega, by omega, rfl⟩
    refine postage_stamp_number_neg_two_of_odd_sandwich _ 1
      (fun A hA hneg => postage_stamp_basis_range_add_one_le_of_neg_of_odd _ (by omega)
        (by omega) A hA hneg) _ hcard ⟨-(2 * (r : ℤ) + 2), by simp, by
          have : (0 : ℤ) ≤ r := Nat.cast_nonneg r
          omega⟩ ?_
    have := postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine r
    omega
  · have hup := fun A hA hneg => postage_stamp_basis_range_add_two_le_of_neg_of_odd (2*m+1)
      (by omega) ho h9 A hA hneg
    rcases (show m % 3 = 2 ∨ m % 3 ≠ 2 by omega) with h3 | h3
    · obtain ⟨r, hr⟩ : ∃ r, m = 6 * r + 2 := ⟨m / 6, by omega⟩
      have hh' : 2 * m + 1 = 12 * r + 5 := by omega
      rw [hh'] at hup ⊢
      have hcard : ({-(2 * (r : ℤ) + 1), 2 * (r : ℤ) + 1, 4 * (r : ℤ) + 4} : Finset ℤ).card = 3 := by
        have : (0 : ℤ) ≤ r := Nat.cast_nonneg r
        rw [Finset.card_eq_three]
        exact ⟨_, _, _, by omega, by omega, by omega, rfl⟩
      refine postage_stamp_number_neg_two_of_odd_sandwich _ 2 hup _ hcard
        ⟨-(2 * (r : ℤ) + 1), by simp, by
          have : (0 : ℤ) ≤ r := Nat.cast_nonneg r
          omega⟩ ?_
      have := postage_stamp_number_neg_two_of_odd_range_ge (12 * r + 5) (36 * r ^ 2 + 48 * r + 12) _
        (4 * (r : ℤ) + 4) (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          have : (0 : ℤ) ≤ r := Nat.cast_nonneg r
          omega) (postage_stamp_number_neg_two_of_odd_family_e r)
      have hN' : ((12 * r + 5) ^ 2 + 6 * (12 * r + 5) + 1) / 4 = 36 * r ^ 2 + 48 * r + 14 := by
        have h : (12 * r + 5) ^ 2 + 6 * (12 * r + 5) + 1 = 4 * (36 * r ^ 2 + 48 * r + 14) := by ring
        rw [h]
        exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)
      omega
    · have hm3 : 3 ≤ m := by omega
      have hcard : ({-(1 : ℤ), (1 : ℤ) + 1, (m : ℤ) + 1 - 1} : Finset ℤ).card = 3 := by
        have : (3 : ℤ) ≤ m := by exact_mod_cast hm3
        rw [Finset.card_eq_three]
        exact ⟨_, _, _, by omega, by omega, by omega, rfl⟩
      refine postage_stamp_number_neg_two_of_odd_sandwich _ 2 hup _ hcard
        ⟨-(1 : ℤ), by simp, by norm_num⟩ ?_
      have := postage_stamp_number_neg_two_of_odd_range_ge (2 * m + 1) (m ^ 2 + 4 * m + 2 - 2) _
        ((m : ℤ) + 1 - 1) (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          omega) (postage_stamp_number_neg_two_of_odd_family_1 m hm h3)
      rw [hN]
      omega
  · have hm6 : m % 6 = 5 := by omega
    have hm5 : m % 5 ≠ 4 := by omega
    have hm5' : (5 : ℤ) ≤ m := by have : 5 ≤ m := by omega
                                  exact_mod_cast this
    have hcard : ({-(2 : ℤ), (2 : ℤ) + 1, (m : ℤ) + 1 - 2} : Finset ℤ).card = 3 := by
      rw [Finset.card_eq_three]
      exact ⟨_, _, _, by omega, by omega, by omega, rfl⟩
    refine postage_stamp_number_neg_two_of_odd_sandwich _ 3
      (fun A hA hneg => postage_stamp_number_neg_two_of_odd_upper_three _ (by omega) ho
        (by omega) A hA hneg) _ hcard ⟨-(2 : ℤ), by simp, by norm_num⟩ ?_
    have := postage_stamp_number_neg_two_of_odd_range_ge (2 * m + 1) (m ^ 2 + 4 * m + 2 - 3) _
      ((m : ℤ) + 1 - 2) (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        omega) (postage_stamp_number_neg_two_of_odd_family_2 m (by omega) hm6 hm5)
    rw [hN]
    have : 3 ≤ m ^ 2 + 4 * m + 2 := by nlinarith
    omega
