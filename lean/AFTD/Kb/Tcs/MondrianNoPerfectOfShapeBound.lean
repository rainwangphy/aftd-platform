import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianShapeBound
import AFTD.Kb.Tcs.MondrianPerfectAreaProduct
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianPartitionBounds
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_no_perfect_of_shape_bound

Topic: combinatorics   Node: 8fa79a11a4a9

Provenance: helper lemma. arXiv:2610.19193, Section 1, and arXiv:2311.02385, Section 3 (available integer dimension pairs); helper for OP-280 and mondrian_no_perfect_partition.

There is no perfect n-square partition if, for every k at least two and positive A with k times A equal to n squared, fewer than k distinct dimension pairs of area A fit in the square.
-/

theorem mondrian_no_perfect_of_shape_bound (n : ℕ)
    (hbound : ∀ k A : ℕ, 2 ≤ k → 0 < A → k * A = n ^ 2 →
      (mondrian_factor_shapes n A).card < k) :
    ¬ ∃ P, mondrian_is_partition n P ∧ mondrian_defect P = 0 := by
  rintro ⟨P, hp, hz⟩
  cases P with
  | nil => have := hp.1; simp at this
  | cons r P =>
    have hr : r ∈ r :: P := by simp
    have hb := mondrian_partition_bounds n (r :: P) hp r hr
    have hA := Nat.mul_pos hb.2.2.1 hb.2.2.2.1
    have hc := mondrian_shape_bound n (mondrian_rect_area r) (r :: P) hp
      (fun s hs => mondrian_defect_zero_equal (r :: P) hz s r hs hr)
    have he := mondrian_perfect_area_product n (r :: P) hp hz r hr
    have hlt := hbound (r :: P).length (mondrian_rect_area r) hp.1 hA he
    omega
