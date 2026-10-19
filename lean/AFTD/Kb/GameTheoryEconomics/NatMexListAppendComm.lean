import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexList
import AFTD.Kb.GameTheoryEconomics.NatMexListNotMemAndLt

/-!
# nat_mex_list_append_comm

Topic: combinatorial_games   Node: f37b3b37fd78

Provenance: helper lemma. step towards spider_blocked_incoming_one_inward

For any two lists of natural numbers l1 and l2, nat_mex_list (l1 ++ l2) = nat_mex_list (l2 ++ l1).
-/

/-- The mex of the concatenation of two lists does not depend on the order of concatenation. -/
theorem nat_mex_list_append_comm (l1 l2 : List ℕ) :
    nat_mex_list (l1 ++ l2) = nat_mex_list (l2 ++ l1) := by
  have h1 := nat_mex_list_not_mem_and_lt (l1 ++ l2)
  have h2 := nat_mex_list_not_mem_and_lt (l2 ++ l1)
  have h_iff (k : ℕ) : k ∈ l1 ++ l2 ↔ k ∈ l2 ++ l1 := by
    simp [List.mem_append, or_comm]
  rcases lt_trichotomy (nat_mex_list (l1 ++ l2)) (nat_mex_list (l2 ++ l1)) with hlt | heq | hgt
  · have := h2.2 (nat_mex_list (l1 ++ l2)) hlt
    rw [← h_iff] at this
    exact (h1.1 this).elim
  · exact heq
  · have := h1.2 (nat_mex_list (l2 ++ l1)) hgt
    rw [h_iff] at this
    exact (h2.1 this).elim
