import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexListNotMemAndLt
import AFTD.Kb.GameTheoryEconomics.NatMexList

/-!
# nat_mex_list_eq_zero

Topic: combinatorial_games   Node: be42723b7bc7

Provenance: helper lemma. step towards spider_grundy_val_one_two

If a list of naturals does not contain 0, then its mex (minimum excluded value) is 0.
-/

/-- The mex of a list not containing 0 is 0. -/
theorem nat_mex_list_eq_zero (l : List ℕ) (h : 0 ∉ l) : nat_mex_list l = 0 := by
  by_contra hne
  exact h ((nat_mex_list_not_mem_and_lt l).2 0 (Nat.pos_of_ne_zero hne))
