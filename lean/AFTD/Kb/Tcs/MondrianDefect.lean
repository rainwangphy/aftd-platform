import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectArea

/-!
# mondrian_defect

Topic: combinatorics   Node: e7272ff721df

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Sec. 1 (def(P)).

The defect def(P) = max_{R∈P} |R| − min_{R∈P} |R| of a family of rectangles.
-/

/-- The defect: largest minus smallest rectangle area. -/
def mondrian_defect (P : List (ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  ((P.map mondrian_rect_area).max?.getD 0) - ((P.map mondrian_rect_area).min?.getD 0)
