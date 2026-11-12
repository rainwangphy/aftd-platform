import AFTD.Prelude
import AFTD.Kb.Tcs.LongestCommonPrefix

/-!
# longest_common_prefix_nil_left

Topic: combinatorics   Node: f8a1c2cad407

Provenance: helper lemma. arXiv:2611.13676 Lemma 3.1

The longest common prefix of the empty list and any list is empty.
-/

/-- The longest common prefix with an empty list on the left is empty. -/
theorem longest_common_prefix_nil_left {α : Type*} [DecidableEq α] (l : List α) :
    longest_common_prefix [] l = [] := by
  cases l <;> rfl
