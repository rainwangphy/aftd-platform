import AFTD.Prelude

/-!
# torusDistance

Topic: circuits   Node: 3aab32f0bb1c

Provenance: formalization of a published result. Source: arXiv:2610.19174, Section 2.1 and Listing A.1

The distance on the one-dimensional torus R/Z, defined as the distance of a real number to the nearest integer.
-/

/-- Distance of a real number to the nearest integer. -/
noncomputable def torusDistance (u : ℝ) : ℝ := |u - (round u : ℝ)|
