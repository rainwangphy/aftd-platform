import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianCellsUnionSum
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectHorizontalMoment
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCongruent

/-!
# mondrian_partition_horizontal_moment

Topic: combinatorics   Node: 04354b1e9c1c

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

For every integer-valued function f on row levels, the sum over an admissible n-square partition of width times the increment of f across each tile is n times (f(n)-f(0)).
-/

open scoped BigOperators

theorem mondrian_partition_horizontal_moment (n : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : mondrian_is_partition n P) (f : ℕ → ℤ) :
    (P.map (fun r => (mondrian_rect_width r : ℤ) *
      (f r.2.2.2 - f r.2.2.1))).sum = (n : ℤ) * (f n - f 0) := by
  have hu := mondrian_cells_union_sum P (hp.2.2.1.imp fun h => h.1)
    (fun c => f (c.2 + 1) - f c.2)
  have hm : P.map (fun r => ∑ c ∈ mondrian_rect_cells r,
      (f (c.2 + 1) - f c.2)) =
      P.map (fun r => (mondrian_rect_width r : ℤ) *
        (f r.2.2.2 - f r.2.2.1)) := by
    apply List.map_congr_left
    intro r hr
    exact mondrian_rect_horizontal_moment r (Nat.le_of_lt (hp.2.1 r hr).2) f
  rw [hm, hp.2.2.2] at hu
  rw [← hu]
  simp only [Finset.sum_product]
  have hsum : ∑ y ∈ Finset.range n, (f (y + 1) - f y) = f n - f 0 :=
    Finset.sum_range_sub f n
  simp only [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
