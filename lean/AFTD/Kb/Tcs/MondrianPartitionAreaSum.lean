import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianCellsUnionCard
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent

/-!
# mondrian_partition_area_sum

Topic: combinatorics   Node: 8fe7b922380f

Provenance: helper lemma. arXiv:2610.19193, Section 1, and arXiv:2311.02385, Section 3 (available integer dimension pairs); helper for OP-280 and mondrian_no_perfect_partition.

The areas of an admissible partition of the n-square sum to n squared.
-/

theorem mondrian_partition_area_sum (n : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (h : mondrian_is_partition n P) :
    (P.map mondrian_rect_area).sum = n ^ 2 := by
  have hc := mondrian_cells_union_card P (h.2.2.1.imp fun h => h.1)
  rw [h.2.2.2] at hc
  simpa [pow_two] using hc.symm
