import AFTD.Prelude

/-!
# is_R_pattern_singleton

Topic: combinatorics   Node: e5454e534ea8

Provenance: helper lemma. arXiv:2610.37940 Section 6.3

The singleton list [1] is an R-pattern.
-/

/-- The singleton list is an R-pattern. -/
theorem is_R_pattern_singleton : ∃ h : [1] ≠ [], ∀ x ∈ [1], x ≤ [1].getLast h := ⟨by decide, by simp⟩
