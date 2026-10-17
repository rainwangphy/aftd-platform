import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampNumber
import AFTD.Kb.NumberTheory.PostageStampNumberNeg
import AFTD.Kb.NumberTheory.PostageStampNumberThreeEightEq
import AFTD.Kb.NumberTheory.PostageStampNumberNegThreeEightGe
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_number_three_eight_lt_neg

Topic: elementary_number_theory   Node: b7611d99543c

Provenance: original. Related work: Smallest case of the four-stamp question; arXiv:2610.19470 (Positivity and negativity for h-bases for n), Theorems 3.3 and 3.4 and Section 4: for three-element sets (k = 2), n♭_h(2) ≤ n_h(2) for every h, with equality exactly for even h ≠ 4. Experiments 724-726.

With four stamps and h = 8, allowing a negative denomination strictly helps: n_8(3) = 89 < 99 ≤ n♭_8(3). (For three stamps the opposite holds for every h.)
-/

theorem postage_stamp_number_three_eight_lt_neg : postage_stamp_number 8 3 < postage_stamp_number_neg 8 3 := by
  rw [postage_stamp_number_three_eight_eq]
  have := postage_stamp_number_neg_three_eight_ge
  omega
