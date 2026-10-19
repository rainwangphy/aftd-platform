import AFTD.Prelude
import AFTD.Kb.Tcs.PellWord
import AFTD.Kb.Tcs.PellWordPrefix

/-!
# pell_word_eq_prefix

Topic: automata   Node: b783e082a45e

Provenance: helper lemma. step towards pell_nfa_run_count_lower_bound

The word u_n is the prefix v_(n-2) of the block-by-block sequence.
-/

lemma pell_word_eq_prefix_aux (j : ℕ) :
    pell_word_prefix j = ((List.range j).map (· + 1)).flatMap (fun i =>
      [⟨i % 5, Nat.mod_lt _ (by decide)⟩, ⟨(i + 1) % 5, Nat.mod_lt _ (by decide)⟩]) := by
  induction j with
  | zero =>
    rfl
  | succ j ih =>
    rw [pell_word_prefix, ih]
    rw [List.range_succ, List.map_append, List.flatMap_append]
    simp only [List.map_cons, List.map_nil, List.flatMap_singleton]

/-- pell_word n is the j-fold block prefix with j = n - 2. -/
theorem pell_word_eq_prefix (n : ℕ) : pell_word n = pell_word_prefix (n - 2) := by
  rw [pell_word, pell_word_eq_prefix_aux]
