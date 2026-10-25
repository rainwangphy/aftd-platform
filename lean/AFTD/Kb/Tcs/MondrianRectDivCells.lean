import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIntervalDiv
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectDiv

/-!
# mondrian_rect_div_cells

Topic: combinatorics   Node: f0a6a5ae37da

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

Membership in a coordinatewise divided rectangle is equivalent to membership of the corresponding last cell of the original square block.
-/

theorem mondrian_rect_div_cells (a : ℕ) (ha : 0 < a)
    (r : ℕ × ℕ × ℕ × ℕ) (i j : ℕ) :
    (i, j) ∈ mondrian_rect_cells (mondrian_rect_div a r) ↔
      (a * (i + 1) - 1, a * (j + 1) - 1) ∈ mondrian_rect_cells r := by
  simp only [mondrian_rect_div, mondrian_rect_cells,
    Finset.mem_product, Finset.mem_Ico]
  rw [mondrian_interval_div a r.1 r.2.1 i ha,
    mondrian_interval_div a r.2.2.1 r.2.2.2 j ha]
