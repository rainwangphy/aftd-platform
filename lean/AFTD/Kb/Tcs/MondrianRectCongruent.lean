import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectHeight

/-!
# mondrian_rect_congruent

Topic: combinatorics   Node: f42ea7ef2ac2

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Sec. 1 (pairwise noncongruent, including after rotation).

Two rectangles are congruent when they have the same side lengths, possibly after a rotation (so 2×3 and 3×2 are congruent).
-/

/-- Congruence of rectangles, rotations allowed. -/
def mondrian_rect_congruent (r s : ℕ × ℕ × ℕ × ℕ) : Prop :=
  (mondrian_rect_width r = mondrian_rect_width s ∧ mondrian_rect_height r = mondrian_rect_height s) ∨
    (mondrian_rect_width r = mondrian_rect_height s ∧ mondrian_rect_height r = mondrian_rect_width s)
