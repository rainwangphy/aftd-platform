import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampNumberNeg
import AFTD.Kb.NumberTheory.PostageStampBasisRangeAddOneLeOfNegOfOdd
import AFTD.Kb.NumberTheory.PostageStampBasisRangeNegGeOfModTwelveEqNine
import AFTD.Kb.NumberTheory.PostageStampBasisRangeAddTwoLeOfNegOfOdd
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# postage_stamp_number_neg_two_add_one_eq_iff

Topic: elementary_number_theory   Node: 38bc8c98c6ff

Provenance: original. Related work: original question (2026-10-23), from arXiv:2610.19470 Theorem 4.1 (n♭_h(2) < n_h(2) for odd h), which leaves the exact value open

For odd h ≥ 5, the negative-allowed three-stamp number misses n_h(2) = ⌊(h²+6h+1)/4⌋ by exactly one, n♭_h(2) = n_h(2) - 1, if and only if h ≡ 9 (mod 12).
-/

theorem postage_stamp_number_neg_two_add_one_eq_iff (h : ℕ) (hh : 5 ≤ h) (ho : h % 2 = 1) :
    postage_stamp_number_neg h 2 + 1 = (h ^ 2 + 6 * h + 1) / 4 ↔ h % 12 = 9 := by
  have hub : ∀ n ∈ {n | ∃ A : Finset ℤ, A.card = 2 + 1 ∧ (∃ a ∈ A, a < 0) ∧
      postage_stamp_basis_range h A = n}, n + 1 ≤ (h ^ 2 + 6 * h + 1) / 4 := by
    rintro n ⟨A, hA, hneg, rfl⟩
    exact postage_stamp_basis_range_add_one_le_of_neg_of_odd h (by omega) ho A hA hneg
  have hbdd : BddAbove {n | ∃ A : Finset ℤ, A.card = 2 + 1 ∧ (∃ a ∈ A, a < 0) ∧
      postage_stamp_basis_range h A = n} :=
    ⟨(h ^ 2 + 6 * h + 1) / 4, fun n hn => by have := hub n hn; omega⟩
  have hne : {n | ∃ A : Finset ℤ, A.card = 2 + 1 ∧ (∃ a ∈ A, a < 0) ∧
      postage_stamp_basis_range h A = n}.Nonempty :=
    ⟨_, {-1, 0, 1}, by rfl, ⟨-1, by simp, by norm_num⟩, rfl⟩
  have h25 : 25 ≤ h ^ 2 := by nlinarith
  have hle : postage_stamp_number_neg h 2 + 1 ≤ (h ^ 2 + 6 * h + 1) / 4 := by
    have := csSup_le hne (fun n hn => show n ≤ (h ^ 2 + 6 * h + 1) / 4 - 1 by
      have := hub n hn; omega)
    unfold postage_stamp_number_neg
    omega
  constructor
  · intro heq
    by_contra h9
    have h2 : ∀ n ∈ {n | ∃ A : Finset ℤ, A.card = 2 + 1 ∧ (∃ a ∈ A, a < 0) ∧
        postage_stamp_basis_range h A = n}, n + 2 ≤ (h ^ 2 + 6 * h + 1) / 4 := by
      rintro n ⟨A, hA, hneg, rfl⟩
      exact postage_stamp_basis_range_add_two_le_of_neg_of_odd h hh ho h9 A hA hneg
    have := csSup_le hne (fun n hn => show n ≤ (h ^ 2 + 6 * h + 1) / 4 - 2 by
      have := h2 n hn; omega)
    unfold postage_stamp_number_neg at heq
    omega
  · intro h9
    obtain ⟨r, rfl⟩ : ∃ r, h = 12 * r + 9 := ⟨h / 12, by omega⟩
    have hcard : ({-(2 * (r : ℤ) + 2), 2 * (r : ℤ) + 2, 4 * (r : ℤ) + 5} : Finset ℤ).card = 2 + 1 := by
      have : (0 : ℤ) ≤ r := Nat.cast_nonneg r
      rw [Finset.card_eq_three]
      exact ⟨_, _, _, by omega, by omega, by omega, rfl⟩
    have hmem : postage_stamp_basis_range (12 * r + 9)
        {-(2 * (r : ℤ) + 2), 2 * (r : ℤ) + 2, 4 * (r : ℤ) + 5} ∈
        {n | ∃ A : Finset ℤ, A.card = 2 + 1 ∧ (∃ a ∈ A, a < 0) ∧
          postage_stamp_basis_range (12 * r + 9) A = n} :=
      ⟨_, hcard, ⟨-(2 * (r : ℤ) + 2), by simp, by
        have : (0 : ℤ) ≤ r := Nat.cast_nonneg r
        omega⟩, rfl⟩
    have hge := postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine r
    have := le_csSup hbdd hmem
    unfold postage_stamp_number_neg at hle ⊢
    omega
