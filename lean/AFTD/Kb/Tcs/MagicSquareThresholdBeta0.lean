import AFTD.Prelude

/-!
# magic_square_threshold_beta0

Topic: quantum   Node: b08402d070d3

Provenance: formalization of a published result. Source: arXiv:2610.12001 Eq. 20

The magic square threshold score beta_0 is (2 + Real.sqrt(2/3))/3.
-/

/-- The threshold score beta_0 in the magic square game above which Alice's key ceases to be perfectly predictable. -/
noncomputable def magic_square_threshold_beta0 : ℝ := (2 + Real.sqrt (2 / 3)) / 3
