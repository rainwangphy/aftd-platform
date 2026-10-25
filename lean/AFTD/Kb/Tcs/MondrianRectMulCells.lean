import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectMul

/-!
# mondrian_rect_mul_cells

Topic: combinatorics   Node: adba7e0835a0

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

A cell belongs to a rectangle with coordinates multiplied by positive a exactly when its quotient cell belongs to the original rectangle.
-/

theorem mondrian_rect_mul_cells (a : ℕ) (ha : 0 < a)
    (r : ℕ × ℕ × ℕ × ℕ) (i j : ℕ) :
    (i, j) ∈ mondrian_rect_cells (mondrian_rect_mul a r) ↔
      (i / a, j / a) ∈ mondrian_rect_cells r := by
  simp only [mondrian_rect_mul, mondrian_rect_cells, Finset.mem_product, Finset.mem_Ico]
  rw [Nat.le_div_iff_mul_le ha, Nat.div_lt_iff_lt_mul ha,
    Nat.le_div_iff_mul_le ha, Nat.div_lt_iff_lt_mul ha]
  simp only [Nat.mul_comm]
