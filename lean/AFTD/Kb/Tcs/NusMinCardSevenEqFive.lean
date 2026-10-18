import AFTD.Prelude
import AFTD.Kb.Tcs.NusMinCard
import AFTD.Kb.Tcs.NusMinCardLeOfHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetHasNoUniqueSumsUnivZmod
import AFTD.Kb.Tcs.FinsetHasNoUniqueSumsDecidable
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums

/-!
# nus_min_card_seven_eq_five

Topic: combinatorics   Node: 60d68e983607

Provenance: helper lemma. step towards nus_min_card_ge_c_log_sq

The minimal size of a set with no unique sums in Z/7Z is exactly 5 (witness {0,1,2,3,4}; every set of size ≤ 4 fails).
-/

/-- m(7) = 5: the least NUS subset of Z/7Z has five elements. -/
theorem nus_min_card_seven_eq_five : nus_min_card 7 = 5 := by
  have hno : ∀ A : Finset (ZMod 7), A.card ≤ 4 → ¬ finset_has_no_unique_sums A := by decide
  refine le_antisymm ?_ ?_
  · exact nus_min_card_le_of_has_no_unique_sums ({0,1,2,3,4} : Finset (ZMod 7)) (by decide)
  · unfold nus_min_card
    refine le_csInf ⟨5, {0,1,2,3,4}, by decide, rfl⟩ ?_
    rintro b ⟨A, hA, rfl⟩
    by_contra h
    exact hno A (by omega) hA
