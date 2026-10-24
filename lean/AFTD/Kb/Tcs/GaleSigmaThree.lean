import AFTD.Prelude

/-!
# gale_sigma_three

Topic: combinatorics   Node: 9d6c56e53fdd

Provenance: formalization of a published result. Source: arXiv:2610.28828, Sec. 2

The real constant `gale_sigma_three` is defined as the square root of (3 + sqrt(3)) / 6.
-/

/-- The real constant sigma_3 = sqrt((3 + sqrt 3) / 6) for Gale's conjecture in dimension 3. -/
noncomputable def gale_sigma_three : ℝ := Real.sqrt ((3 + Real.sqrt 3) / 6)
