import AFTD.Prelude

/-!
# pell_word_prefix

Topic: automata   Node: 054ba7e9440e

Provenance: helper lemma. step towards pell_nfa_run_count_lower_bound

The prefix v_j of u_n consisting of its first j two-letter blocks, v_j = c_1c_2 c_2c_3 … c_jc_(j+1), built by appending one block at a time; v_0 = [] and v_(j+1) = v_j ++ [c_(j+1), c_(j+2)].
-/

/-- The prefix of pell_word n consisting of its first j two-letter blocks. -/
def pell_word_prefix : ℕ → List (Fin 5)
  | 0 => []
  | i + 1 => pell_word_prefix i ++
      [⟨(i + 1) % 5, Nat.mod_lt _ (by decide)⟩, ⟨(i + 2) % 5, Nat.mod_lt _ (by decide)⟩]
