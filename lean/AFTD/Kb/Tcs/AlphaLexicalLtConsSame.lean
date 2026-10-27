import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# alpha_lexical_lt_cons_same

Topic: combinatorics   Node: fd7daf0cfa70

Provenance: helper lemma. step towards alpha_lexical_lt_iff_inverse_prefix

Prepending the same head to both sequences reverses the alternating lexical order on their tails.
-/

lemma alpha_lexical_lt_cons_same_signed_succ (x : ℕ) (xs : List ℕ) (j : ℕ) :
    alpha_signed_cell (x :: xs) (j + 1) = -alpha_signed_cell xs j := by
  simp only [alpha_signed_cell, List.getD_cons_succ]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg (by omega), neg_neg]

/-- Prepending the same head to both sequences reverses the alternating lexical order on their tails. -/
theorem alpha_lexical_lt_cons_same (x : ℕ) (xs ys : List ℕ) :
    alpha_lexical_lt (x :: xs) (x :: ys) ↔ alpha_lexical_lt ys xs := by
  constructor
  · rintro ⟨i, hi, heq, hlt⟩
    cases i with
    | zero => simp [alpha_signed_cell] at hlt
    | succ j =>
      refine ⟨j, ?_, fun k hk => ?_, ?_⟩
      · simp only [List.length_cons] at hi; omega
      · have := heq (k + 1) (by omega)
        rw [alpha_lexical_lt_cons_same_signed_succ, alpha_lexical_lt_cons_same_signed_succ] at this
        linarith
      · rw [alpha_lexical_lt_cons_same_signed_succ, alpha_lexical_lt_cons_same_signed_succ] at hlt
        linarith
  · rintro ⟨j, hj, heq, hlt⟩
    refine ⟨j + 1, ?_, fun k hk => ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · cases k with
      | zero => rfl
      | succ k =>
        rw [alpha_lexical_lt_cons_same_signed_succ, alpha_lexical_lt_cons_same_signed_succ,
          heq k (by omega)]
    · rw [alpha_lexical_lt_cons_same_signed_succ, alpha_lexical_lt_cons_same_signed_succ]
      linarith
