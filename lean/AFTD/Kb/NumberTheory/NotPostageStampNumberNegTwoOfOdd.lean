import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampNumberNeg
import AFTD.Kb.NumberTheory.PostageStampBasisRangeAddOneLeOfNegOfOdd
import AFTD.Kb.NumberTheory.PostageStampBasisRangeNegGeOfModTwelveEqNine
import AFTD.Kb.NumberTheory.PostageStampBasisRangeAddTwoLeOfNegOfOdd
import AFTD.Kb.NumberTheory.PostageStampNumberNegFourOneNineTwoAddSixLe

/-!
# not_postage_stamp_number_neg_two_of_odd

Topic: elementary_number_theory   Node: f3d07737e560

Provenance: original. Related work: refutes `postage_stamp_number_neg_two_of_odd`

The statement `postage_stamp_number_neg_two_of_odd` is false: at h = 419 (h ≡ 59 mod 60) the conjecture predicts n♭_h(2) = n_h(2) - 4, but postage_stamp_number_neg_four_one_nine_two_add_six_le proves n♭_419(2) ≤ n_419(2) - 6
-/

theorem not_postage_stamp_number_neg_two_of_odd : ¬ (∀ (h : ℕ) (hh : 5 ≤ h) (ho : h % 2 = 1), postage_stamp_number_neg h 2 +
        (if h % 12 = 9 then 1 else if h % 12 ≠ 11 then 2 else if h % 60 = 59 then 4 else 3) =
      (h ^ 2 + 6 * h + 1) / 4) := by
  intro hall
  have h1 := hall 419 (by norm_num) (by norm_num)
  have h2 := postage_stamp_number_neg_four_one_nine_two_add_six_le
  norm_num at h1 h2
  omega
