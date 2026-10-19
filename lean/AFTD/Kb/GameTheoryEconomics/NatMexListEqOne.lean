import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexListNotMemAndLt
import AFTD.Kb.GameTheoryEconomics.NatMexList

/-!
# nat_mex_list_eq_one

Topic: combinatorial_games   Node: 7cc89f9cd6f9

Provenance: helper lemma. step towards spider_grundy_val_one_two

If a list of naturals contains 0 but not 1, then its mex is 1.
-/

/-- The mex of a list containing 0 but not 1 is 1. -/
theorem nat_mex_list_eq_one (l : List ℕ) (h0 : 0 ∈ l) (h1 : 1 ∉ l) : nat_mex_list l = 1 := by
  obtain ⟨hnot, hlt⟩ := nat_mex_list_not_mem_and_lt l
  have h_ne_zero : nat_mex_list l ≠ 0 := by
    intro h
    apply hnot
    rw [h]
    exact h0
  have h_le_one : nat_mex_list l ≤ 1 := by
    by_contra! h2
    have : 1 ∈ l := hlt 1 h2
    exact h1 this
  omega
