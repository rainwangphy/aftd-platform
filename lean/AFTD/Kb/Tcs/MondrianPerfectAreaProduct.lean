import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianPartitionAreaSum
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianRectArea

/-!
# mondrian_perfect_area_product

Topic: combinatorics   Node: badc0ca3d22e

Provenance: helper lemma. arXiv:2610.19193, Section 1, and arXiv:2311.02385, Section 3 (available integer dimension pairs); helper for OP-280 and mondrian_no_perfect_partition.

In a perfect n-square partition, the number of rectangles times the area of any member is n squared.
-/

theorem mondrian_perfect_area_product (n : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (h : mondrian_is_partition n P) (hz : mondrian_defect P = 0)
    (r : ℕ × ℕ × ℕ × ℕ) (hr : r ∈ P) :
    P.length * mondrian_rect_area r = n ^ 2 := by
  rw [← mondrian_partition_area_sum n P h]
  have heq : P.map mondrian_rect_area = List.replicate P.length (mondrian_rect_area r) := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp, ?_⟩
    intro a ha
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
    exact mondrian_defect_zero_equal P hz s r hs hr
  rw [heq]
  simp
