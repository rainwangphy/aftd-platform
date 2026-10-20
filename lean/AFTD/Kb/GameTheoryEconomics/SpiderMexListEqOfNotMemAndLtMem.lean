import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.NatMexListNotMemAndLt

/-!
# spider_mex_list_eq_of_not_mem_and_lt_mem

Topic: combinatorial_games   Node: fcc9db6c5797

Provenance: helper lemma. step towards spider_two_leg_blocked_incoming_val

If a natural number m is absent from a list l of naturals and every k < m is present in l, then the mex of l is m.
-/

/-- Converse characterisation of the mex: absence of m together with coverage of the initial segment below m pins the mex to m. -/
theorem spider_mex_list_eq_of_not_mem_and_lt_mem (l : List ℕ) (m : ℕ) (hm : m ∉ l)
    (hlt : ∀ k < m, k ∈ l) : nat_mex_list l = m := by
  rcases nat_mex_list_not_mem_and_lt l with ⟨hnot, hcov⟩
  apply Nat.le_antisymm
  · by_contra h
    exact hm (hcov m (Nat.lt_of_not_le h))
  · by_contra h
    exact hnot (hlt (nat_mex_list l) (Nat.lt_of_not_le h))
