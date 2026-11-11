import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesFiber35WidthGapCaseD7
import AFTD.Kb.NumberTheory.GoodSlopesFiber35WidthGapCaseD1pmpp
import AFTD.Kb.NumberTheory.GoodSlopesFiber35WidthGapCaseD1pp
import AFTD.Kb.NumberTheory.GoodSlopesFiber35WidthGapCaseD5
import AFTD.Kb.NumberTheory.GoodSlopesFiber35WidthGapCaseD1mp
import AFTD.Kb.NumberTheory.GoodSlopesFiber35WidthGapCaseD1mm
import AFTD.Kb.NumberTheory.GoodSlopesFiber35WidthGapCaseD1pmpm
import AFTD.Kb.NumberTheory.GoodSlopesFiber35WidthGapCaseD1pmm

/-!
# good_slopes_fiber35_anchored_width_gap

Topic: elementary_number_theory   Node: 50889fe36cbd

Provenance: helper lemma. A finite reduction of the colored-fiber lemma for OP-1027, exhaustively checked by CP-SAT in experiment 22119 and independently encoded into UNSAT CNF for d=1 and d=5; the SAT certificates are not yet checked in Lean.

A 35-point set modulo 35 containing (0,0) and (d,-d), with d equal to 1, 5 or 7, has at most 16 good unit directions if each x-fiber and the collision line have at most three points and every bad unit direction has at least three bad neighbors.
-/

theorem good_slopes_fiber35_anchored_width_gap (S : Finset (ZMod 35 × ZMod 35)) (hcard : S.card = 35)
  (d : ZMod 35) (hd : d = 1 ∨ d = 5 ∨ d = 7)
  (h0 : (0,0) ∈ S) (h1 : (d,-d) ∈ S)
  (hx : ∀ x : ZMod 35, (S.filter (fun p => p.1 = x)).card ≤ 3)
  (hline : (S.filter (fun p => p.2 + p.1 = 0)).card ≤ 3)
  (hneighbors : ∀ a : ZMod 35, IsUnit a → a ∉ good_slopes_point_directions 35 S →
    ((good_slopes_point_directions 35 S).filter (fun b => b ≠ a ∧ (b.val % 5 = a.val % 5 ∨ b.val % 7 = a.val % 7))).card ≤ 5) :
  (good_slopes_point_directions 35 S).card ≤ 16 := by
  rcases hd with rfl | rfl | rfl
  · have e : (-(1 : ZMod 35)) = 34 := by decide
    rw [e] at h1
    by_cases h2 : (2 : ZMod 35) ∈ good_slopes_point_directions 35 S
    · by_cases h29 : (29 : ZMod 35) ∈ good_slopes_point_directions 35 S
      · exact good_slopes_fiber35_width_gap_case_d1pp S hcard h0 h1 hx hline hneighbors h2 h29
      · by_cases h4 : (4 : ZMod 35) ∈ good_slopes_point_directions 35 S
        · by_cases h8 : (8 : ZMod 35) ∈ good_slopes_point_directions 35 S
          · exact good_slopes_fiber35_width_gap_case_d1pmpp S hcard h0 h1 hx hline hneighbors h2 h4 h8 h29
          · exact good_slopes_fiber35_width_gap_case_d1pmpm S hcard h0 h1 hx hline hneighbors h2 h4 h29 h8
        · exact good_slopes_fiber35_width_gap_case_d1pmm S hcard h0 h1 hx hline hneighbors h2 h29 h4
    · by_cases h29 : (29 : ZMod 35) ∈ good_slopes_point_directions 35 S
      · exact good_slopes_fiber35_width_gap_case_d1mp S hcard h0 h1 hx hline hneighbors h29 h2
      · exact good_slopes_fiber35_width_gap_case_d1mm S hcard h0 h1 hx hline hneighbors h2 h29
  · have e : (-(5 : ZMod 35)) = 30 := by decide
    rw [e] at h1
    exact good_slopes_fiber35_width_gap_case_d5 S hcard h0 h1 hx hline hneighbors
  · have e : (-(7 : ZMod 35)) = 28 := by decide
    rw [e] at h1
    exact good_slopes_fiber35_width_gap_case_d7 S hcard h0 h1 hx hline hneighbors
