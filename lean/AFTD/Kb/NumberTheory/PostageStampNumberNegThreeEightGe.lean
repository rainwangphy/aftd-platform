import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.PostageStampNumberNeg
import AFTD.Kb.NumberTheory.PostageStampBasisRangeEightNegFourOneThirteenFourteen
import AFTD.Kb.NumberTheory.PostageStampBasisRangeSuccLeCardPow

/-!
# postage_stamp_number_neg_three_eight_ge

Topic: elementary_number_theory   Node: 6561a379f205

Provenance: helper lemma. Step toward postage_stamp_number_three_lt_neg (four-stamp analogue of arXiv:2610.19470, Theorems 3.3-3.4); the set was found by exhaustive search (experiments 724-726).

n♭_8(3) ≥ 99: some 4-element set of integers with a negative element is an 8-basis for 99 (namely {−4, 1, 13, 14}).
-/

theorem postage_stamp_number_neg_three_eight_ge : 99 ≤ postage_stamp_number_neg 8 3 := by
  have hA_card : ({-4, 1, 13, 14} : Finset ℤ).card = 3 + 1 := by decide
  have hA_neg : ∃ a ∈ ({-4, 1, 13, 14} : Finset ℤ), a < 0 := by
    use -4
    simp
  have h_in : postage_stamp_basis_range 8 {-4, 1, 13, 14} ∈
      {n | ∃ A : Finset ℤ, A.card = 3 + 1 ∧ (∃ a ∈ A, a < 0) ∧ postage_stamp_basis_range 8 A = n} := by
    refine ⟨{-4, 1, 13, 14}, hA_card, hA_neg, rfl⟩
  have h_bdd : BddAbove {n : ℕ | ∃ A : Finset ℤ, A.card = 3 + 1 ∧ (∃ a ∈ A, a < 0) ∧ postage_stamp_basis_range 8 A = n} := by
    use 4^8
    rintro n ⟨A, hA_card', _, rfl⟩
    have hA_nonempty : A.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp at hA_card'
    have hle := postage_stamp_basis_range_succ_le_card_pow 8 A hA_nonempty
    rw [hA_card'] at hle
    omega
  have h_le := le_csSup h_bdd h_in
  exact le_trans postage_stamp_basis_range_eight_neg_four_one_thirteen_fourteen h_le
