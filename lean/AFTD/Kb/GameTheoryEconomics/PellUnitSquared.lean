import AFTD.Prelude

/-!
# pell_unit_squared

Topic: combinatorial_games   Node: 51c96c41ac1a

Provenance: formalization of a published result. Source: arXiv:2611.05898

The definition of pell_unit_squared as the real number 17 + 12 * Real.sqrt 2.
-/

/-- The real constant 17 + 12 * Real.sqrt 2, the square of the fundamental Pell unit. -/
noncomputable def pell_unit_squared : ℝ := 17 + 12 * Real.sqrt 2
