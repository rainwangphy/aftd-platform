import AFTD.Prelude

/-!
# mondrian_rect_height

Topic: combinatorics   Node: f0f4be3d5f78

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Sec. 1.

The height y₁ − y₀ of the rectangle (x₀, x₁, y₀, y₁).
-/

/-- Height `y₁ - y₀`. -/
def mondrian_rect_height (r : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  r.2.2.2 - r.2.2.1
