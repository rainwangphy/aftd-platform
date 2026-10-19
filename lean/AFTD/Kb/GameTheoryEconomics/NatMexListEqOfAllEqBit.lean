import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NatMexListEqZero
import AFTD.Kb.GameTheoryEconomics.NatMexListEqOne
import AFTD.Kb.GameTheoryEconomics.NatMexList

/-!
# nat_mex_list_eq_of_all_eq_bit

Topic: combinatorial_games   Node: 9ac2c3b9098b

Provenance: helper lemma. step towards spider_blocked_incoming_one_inward

For any list of natural numbers whose elements all equal a single bit b ∈ {0, 1}, if the list is non-empty, its nat_mex_list is 1 - b.
-/

/-- The mex of a non-empty list of natural numbers whose elements all equal a bit b in {0, 1} is 1 - b. -/
theorem nat_mex_list_eq_of_all_eq_bit {l : List ℕ} (b : ℕ) (hb : b = 0 ∨ b = 1)
    (h_all : ∀ x ∈ l, x = b) (h_nonempty : l ≠ []) :
    nat_mex_list l = 1 - b := by
  rcases hb with rfl | rfl
  · rw [Nat.sub_zero]
    apply nat_mex_list_eq_one
    · obtain ⟨x, hx⟩ : ∃ x, x ∈ l := List.exists_mem_of_ne_nil l h_nonempty
      have hx0 := h_all x hx
      subst hx0
      exact hx
    · intro h1
      have h10 := h_all 1 h1
      revert h10
      decide
  · rw [Nat.sub_self]
    apply nat_mex_list_eq_zero
    intro h0
    have h01 := h_all 0 h0
    revert h01
    decide
