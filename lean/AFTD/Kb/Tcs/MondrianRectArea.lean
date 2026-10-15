import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectHeight

/-!
# mondrian_rect_area

Topic: combinatorics   Node: 1c07ed05c376

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Sec. 1 (|R|).

The area |R| = width × height of a rectangle.
-/

/-- Area `|R|`. -/
def mondrian_rect_area (r : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  mondrian_rect_width r * mondrian_rect_height r
