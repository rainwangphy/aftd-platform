import AFTD.Prelude
import AFTD.Kb.Tcs.IsCompleteReturnWord

/-!
# is_complete_return_word_prefix

Topic: combinatorics   Node: eabbbbbc8858

Provenance: helper lemma. arXiv:2611.13676 Section 2

If c is a complete return word to q, then q is a prefix of c.
-/

/-- A complete return word to q has q as a prefix. -/
theorem is_complete_return_word_prefix {α : Type*} {c q : List α}
    (h : is_complete_return_word c q) : q <+: c := by
  exact h.1
