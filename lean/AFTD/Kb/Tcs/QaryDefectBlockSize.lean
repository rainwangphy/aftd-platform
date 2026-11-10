import AFTD.Prelude

/-!
# qary_defect_block_size

Topic: information   Node: bcf9876e688c

Provenance: formalization of a published result. Source: knowledgebase

The function qary_defect_block_size takes two natural numbers d and n and returns the natural number (round (Real.sqrt (2 * (n : ℝ) / (d + 1 : ℝ)))).toNat, computed by taking the square root of the real quotient 2 * (n : ℝ) / (d + 1 : ℝ), rounding to the nearest integer with round, and converting to ℕ with Int.toNat.
-/

/-- Nearest integer defect block spacing for gap d and length n. -/
noncomputable def qary_defect_block_size (d n : ℕ) : ℕ := (round (Real.sqrt (2 * (n : ℝ) / (d + 1 : ℝ)))).toNat
