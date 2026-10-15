import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianSevenRects

/-!
# mondrian_seven_rects_defect_example

Topic: combinatorics   Node: 79ab012d16bb

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Example 1.

For (p, q) = (13, 3) (n = 315) the seven rectangles have defect 280: the largest area is 238×60 = 14280 and the smallest 70×200 = 14000.
-/

theorem mondrian_seven_rects_defect_example : mondrian_defect (mondrian_seven_rects 13 3) = 280 := by first | (simp_all; done) | omega | decide | linarith | positivity | (aesop; done)
