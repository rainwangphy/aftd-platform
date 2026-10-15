import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianMinDefectSeven
import AFTD.Kb.Tcs.MondrianPellFamilyDefect280
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianPellSide

/-!
# mondrian_liminf_min_defect_seven_le

Topic: combinatorics   Node: ada280100458

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Theorem 1.1 ('Consequently liminf M(n) ≤ 280'; the partitions used have seven rectangles, so the bound holds for M₇).

liminf_{n→∞} M₇(n) ≤ 280: infinitely many squares have a seven-rectangle Mondrian partition with defect at most 280.
-/

theorem mondrian_liminf_min_defect_seven_le :
    Filter.liminf (fun n => mondrian_min_defect_seven n) Filter.atTop ≤ 280 := by
  have hgrow : ∀ j, j ≤ mondrian_pell_side j := by
    have key : ∀ j, j + 315 ≤ mondrian_pell_side j ∧ mondrian_pell_side j + 1 ≤ mondrian_pell_side (j + 1) := by
      intro j
      induction j with
      | zero => simp [mondrian_pell_side]
      | succ n ih =>
        obtain ⟨h1, h2⟩ := ih
        have e : mondrian_pell_side (n + 2) = 340 * mondrian_pell_side (n + 1) - mondrian_pell_side n := rfl
        refine ⟨by omega, ?_⟩
        rw [e]; omega
    exact fun j => by have := (key j).1; omega
  apply Filter.liminf_le_of_frequently_le'
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨mondrian_pell_side N, hgrow N, ?_⟩
  obtain ⟨⟨P, hP, hlen, hdef⟩, -⟩ := mondrian_pell_family_defect_280 N
  calc mondrian_min_defect_seven (mondrian_pell_side N) ≤ (mondrian_defect P : ℕ∞) :=
        iInf₂_le P ⟨hP, hlen⟩
    _ = 280 := by rw [hdef]; rfl
