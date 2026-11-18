import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaLexicalLtConsSame

/-!
# alpha_lexical_lt_append_parity

Topic: combinatorics   Node: 8f8d46cb3d0a

Provenance: helper lemma. Common-prefix cancellation helper for OP-392, arXiv:2610.24758; alternating order as in arXiv:0810.5205.

Prepending an even-length common sequence preserves alternating lexical order, while prepending an odd-length common sequence reverses it.
-/

theorem alpha_lexical_lt_append_parity (u x y : List ℕ) :
    alpha_lexical_lt (u ++ x) (u ++ y) ↔
      if u.length % 2 = 0 then alpha_lexical_lt x y else alpha_lexical_lt y x := by
  induction u generalizing x y with
  | nil => simp
  | cons h t ih =>
    simp only [List.cons_append, alpha_lexical_lt_cons_same]
    rw [ih]
    simp only [List.length_cons]
    rcases Nat.mod_two_eq_zero_or_one t.length with h0 | h1
    · have hs : (t.length + 1) % 2 = 1 := by omega
      simp [h0, hs]
    · have hs : (t.length + 1) % 2 = 0 := by omega
      simp [h1, hs]
