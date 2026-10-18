import AFTD.Prelude
import AFTD.Kb.Tcs.NusMinCard
import AFTD.Kb.Tcs.NusMinCardLeOfHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetHasNoUniqueSumsUnivZmod
import AFTD.Kb.Tcs.FinsetHasNoUniqueSumsDecidable
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums

/-!
# nus_min_card_five_eq_four

Topic: combinatorics   Node: 4d105c562705

Provenance: helper lemma. step towards nus_min_card_ge_c_log_sq

The minimal size of a set with no unique sums in Z/5Z is exactly 4 (witness {0,1,2,3}; no set of size ≤ 3 works).
-/

/-- m(5) = 4: the least NUS subset of Z/5Z has four elements. -/
theorem nus_min_card_five_eq_four : nus_min_card 5 = 4 := by
  have hno : ∀ A : Finset (ZMod 5), A.card ≤ 3 → ¬ finset_has_no_unique_sums A := by decide
  refine le_antisymm ?_ ?_
  · exact nus_min_card_le_of_has_no_unique_sums ({0,1,2,3} : Finset (ZMod 5)) (by decide)
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    unfold nus_min_card
    refine le_csInf ?_ ?_
    · exact ⟨(Finset.univ : Finset (ZMod 5)).card, Finset.univ, finset_has_no_unique_sums_univ_zmod (by norm_num), rfl⟩
    · rintro b ⟨A, hA, rfl⟩
      by_contra h
      exact hno A (by omega) hA
