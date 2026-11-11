import AFTD.Prelude
import AFTD.Kb.Tcs.IsLongestWordRun
import AFTD.Kb.Tcs.IsWordRun
import AFTD.Kb.Tcs.IsConstantWord
import AFTD.Kb.Tcs.IsWordRunOfConstant

/-!
# is_longest_word_run_of_constant

Topic: information   Node: 1bae77173ef7

Provenance: helper lemma. folklore

For any constant word y on Fin n with 1 ≤ n, the interval [0, n) is a longest run of y.
-/

/-- For any constant word on Fin n with 1 ≤ n, the interval [0, n) is a longest run. -/
theorem is_longest_word_run_of_constant {n : ℕ} {α : Type*} (y : Fin n → α)
    (hconst : is_constant_word y) (hn : 1 ≤ n) : is_longest_word_run y 0 n := by
  refine ⟨is_word_run_of_constant y hconst hn, ?_⟩
  intro a' b' hr
  obtain ⟨hab, hbn, _⟩ := hr
  omega
