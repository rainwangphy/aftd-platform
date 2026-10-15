import AFTD.Prelude

/-!
# mondrian_rect_width

Topic: combinatorics   Node: 63f5a43ae897

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Sec. 1.

The width x₁ − x₀ of the rectangle (x₀, x₁, y₀, y₁).
-/

/-- Width `x₁ - x₀`. -/
def mondrian_rect_width (r : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  r.2.1 - r.1
