import AFTD.Prelude
import AFTD.Kb.Tcs.PellWordEqPrefix
import AFTD.Kb.Tcs.PellWordPrefix
import AFTD.Kb.Tcs.PellWord

/-!
# pell_word_length

Topic: automata   Node: 0c5982051d9c

Provenance: helper lemma. step towards pell_nfa_run_count_lower_bound

The word u_n = c_1c_2…c_(n-2)c_(n-1) has length 2(n-2).
-/

/-- The word u_n has length 2(n-2). -/
theorem pell_word_length (n : ℕ) : (pell_word n).length = 2 * (n - 2) := by
  rw [pell_word_eq_prefix]
  generalize n - 2 = j
  induction j with
  | zero => rfl
  | succ j ih =>
    simp [pell_word_prefix, ih]
    omega
