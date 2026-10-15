import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianPellSideEq
import AFTD.Kb.Tcs.MondrianPellSideMod
import AFTD.Kb.Tcs.MondrianSevenRectsIsPartition
import AFTD.Kb.Tcs.MondrianSevenRectsDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianSevenRects
import AFTD.Kb.Tcs.MondrianPellSide

/-!
# mondrian_pell_family_defect_280

Topic: combinatorics   Node: 24b3c38fbe01

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Theorem 1.1 (the liminf consequence is stated separately as mondrian_liminf_min_defect_seven_le).

For n₀ = 315, n₁ = 106785, n_{j+2} = 340n_{j+1} − n_j: for every j the n_j×n_j square has a Mondrian partition into seven pairwise noncongruent integer rectangles with defect 280, and n_j ≡ 315 (mod 630).
-/

theorem mondrian_pell_family_defect_280 (j : ℕ) :
    (∃ P, mondrian_is_partition (mondrian_pell_side j) P ∧ P.length = 7 ∧ mondrian_defect P = 280) ∧
      mondrian_pell_side j % 630 = 315 := by
  refine ⟨?_, mondrian_pell_side_mod j⟩
  obtain ⟨p, q, hp1, hq1, hqp, hp7, hE, hn⟩ := mondrian_pell_side_eq j
  have hpar : p % 2 = q % 2 := by omega
  refine ⟨mondrian_seven_rects p q, ?_, by simp [mondrian_seven_rects], ?_⟩
  · rw [hn]
    exact mondrian_seven_rects_is_partition p q hpar hqp hp7
  · have h := mondrian_seven_rects_defect p q hpar hqp hp7
    rw [hE] at h
    norm_num at h
    exact_mod_cast h
