import AFTD.Prelude
import AFTD.Kb.Tcs.PellWordEqPrefix
import AFTD.Kb.Tcs.PellWordPrefix
import AFTD.Kb.Tcs.PellWord

/-!
# pell_word_get

Topic: automata   Node: 7ff1163cefa6

Provenance: helper lemma. step towards pell_nfa_run_count_lower_bound

The j-th letter of u_n is c_(j/2+1) if j is even and c_(j/2+2) if j is odd.
-/

lemma pell_word_get_list_two_zero {α : Type} (a b : α) (i : ℕ) (hi : i = 0) (h : i < [a, b].length) :
    [a, b][i]'h = a := by
  subst hi
  rfl

lemma pell_word_get_list_two_one {α : Type} (a b : α) (i : ℕ) (hi : i = 1) (h : i < [a, b].length) :
    [a, b][i]'h = b := by
  subst hi
  rfl

lemma pell_word_get_prefix_length (j : ℕ) : (pell_word_prefix j).length = 2 * j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp [pell_word_prefix, ih]
    omega

lemma pell_word_get_prefix_get (j i : ℕ) (hi : i < (pell_word_prefix j).length) :
    ((pell_word_prefix j)[i]'hi).val = (i / 2 + 1 + i % 2) % 5 := by
  induction j generalizing i with
  | zero =>
    rw [pell_word_get_prefix_length] at hi
    omega
  | succ j ih =>
    have hj_len : (pell_word_prefix j).length = 2 * j := pell_word_get_prefix_length j
    dsimp only [pell_word_prefix] at hi ⊢
    by_cases h : i < (pell_word_prefix j).length
    · rw [List.getElem_append_left h]
      exact ih i h
    · rw [List.getElem_append_right (by omega)]
      have hi2 : i < 2 * j + 2 := by
        revert hi
        simp only [List.length_append, List.length_cons, List.length_nil, hj_len]
        omega
      have : i = 2 * j ∨ i = 2 * j + 1 := by omega
      rcases this with rfl | rfl
      · rw [pell_word_get_list_two_zero _ _ _ (by omega)]
        have h1 : (2 * j) / 2 = j := by omega
        have h2 : (2 * j) % 2 = 0 := by omega
        rw [h1, h2]
      · rw [pell_word_get_list_two_one _ _ _ (by omega)]
        have h1 : (2 * j + 1) / 2 = j := by omega
        have h2 : (2 * j + 1) % 2 = 1 := by omega
        rw [h1, h2]

/-- The j-th letter of u_n is c_(j/2+1) for j even and c_(j/2+2) for j odd, i.e. of residue (j/2+1+j%2) mod 5. -/
theorem pell_word_get (n j : ℕ) (hj : j < (pell_word n).length) :
    ((pell_word n).get ⟨j, hj⟩).val = (j / 2 + 1 + j % 2) % 5 := by
  have hp : pell_word n = pell_word_prefix (n - 2) := pell_word_eq_prefix n
  revert hj
  rw [hp]
  intro hj
  rw [List.get_eq_getElem]
  exact pell_word_get_prefix_get (n - 2) j hj
