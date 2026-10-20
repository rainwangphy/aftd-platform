import AFTD.Prelude
import AFTD.Kb.Tcs.StandardExampleLe
import AFTD.Kb.Tcs.StandardExample

/-!
# standard_example_partial_order

Topic: combinatorics   Node: 6272510a75f4

Provenance: formalization of a published result. Source: arXiv:2610.24774 Section 1

The standard example of order k is a partial order under standard_example_le.
-/

/-- PartialOrder instance on the standard example of order k. -/
instance standard_example_partial_order (k : ℕ) : PartialOrder (StandardExample k) where
  le := standard_example_le
  le_refl x := by cases x <;> simp [standard_example_le]
  le_trans x y z := by
    cases x <;> cases y <;> cases z <;> simp [standard_example_le]
    · rintro rfl; exact id
    · rintro rfl; exact id
    · rintro h rfl; exact h
    · rintro rfl; exact id
  le_antisymm x y := by
    cases x <;> cases y <;> simp [standard_example_le]
    · rintro rfl _; rfl
    · rintro rfl _; rfl
