import AFTD.Prelude

/-!
# quaternion_group_card

Topic: combinatorics   Node: 31c6b9f0d977

Provenance: helper lemma. Mathlib.GroupTheory.SpecificGroups.Quaternion

For every natural number n, the cardinality of the generalized quaternion group QuaternionGroup (2 * n + 1) is 8 * n + 4.
-/

/-- The order of the generalized quaternion group QuaternionGroup (2 * n + 1) is 8 * n + 4. -/
theorem quaternion_group_card (n : ℕ) :
    Fintype.card (QuaternionGroup (2 * n + 1)) = 8 * n + 4 := by
  have : NeZero (2 * n + 1) := ⟨by omega⟩
  rw [QuaternionGroup.card]
  omega
