import AFTD.Prelude
import AFTD.Kb.Tcs.NusMinCard
import AFTD.Kb.Tcs.NusMinCardGeOneAddClog
import AFTD.Kb.Tcs.FinsetHasNoUniqueSumsUnivZmodThree
import AFTD.Kb.Tcs.NusMinCardLeOfHasNoUniqueSums

/-!
# nus_min_card_three_eq_three

Topic: combinatorics   Node: a0f79834e03c

Provenance: helper lemma. step towards nus_min_card_ge_c_log_sq

The minimal cardinality of a set with no unique sums in Z/3Z is exactly 3.
-/

/-- The minimal cardinality of a set with no unique sums in Z/3Z is exactly 3. -/
theorem nus_min_card_three_eq_three : nus_min_card 3 = 3 := by
  have h1 : 1 + Nat.clog 2 3 ≤ nus_min_card 3 := by
    apply nus_min_card_ge_one_add_clog
    decide
  have h2 : nus_min_card 3 ≤ (Finset.univ : Finset (ZMod 3)).card := by
    apply nus_min_card_le_of_has_no_unique_sums
    exact finset_has_no_unique_sums_univ_zmod_three
  rw [Finset.card_univ, ZMod.card 3] at h2
  have hc : Nat.clog 2 3 = 2 := rfl
  omega
