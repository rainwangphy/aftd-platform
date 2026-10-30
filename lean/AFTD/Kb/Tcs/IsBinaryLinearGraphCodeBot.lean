import AFTD.Prelude
import AFTD.Kb.Tcs.IsBinaryLinearGraphCode

/-!
# is_binary_linear_graph_code_bot

Topic: combinatorics   Node: e261f758de44

Provenance: helper lemma. arXiv:2610.35136, Section 1

The singleton set containing only the empty graph on Fin n is a binary linear graph-code.
-/

/-- The singleton set containing only the empty graph is a binary linear graph-code. -/
theorem is_binary_linear_graph_code_bot (n : ℕ) : is_binary_linear_graph_code n {⊥} := by
  constructor
  · simp
  · intro G G' hG hG'
    simp only [Set.mem_singleton_iff] at hG hG'
    subst hG hG'
    simp [symmDiff_self]
