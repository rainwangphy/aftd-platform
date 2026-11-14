import AFTD.Prelude

/-!
# two_point_mask

Topic: information   Node: a1cc141dbc43

Provenance: formalization of a published result. Source: arXiv:2611.16066, Theorem 5.5

Given a real parameter c, two_point_mask c is the function from ℤ to ℝ mapping 0 to 1 - c, 1 to c, and all other integers to 0.
-/

/-- The two-point probability mass function from ℤ to ℝ assigning mass 1 - c to 0 and c to 1. -/
def two_point_mask (c : ℝ) : ℤ → ℝ := fun s => if s = 0 then 1 - c else if s = 1 then c else 0
