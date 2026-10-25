import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_partition_bounds

Topic: combinatorics   Node: 06cbb796b492

Provenance: helper lemma. arXiv:2610.19193, Section 1, and arXiv:2311.02385, Section 3 (available integer dimension pairs); helper for OP-280 and mondrian_no_perfect_partition.

Every rectangle of an admissible n-square partition has positive side lengths, upper coordinates at most n, and side lengths at most n.
-/

theorem mondrian_partition_bounds (n : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (h : mondrian_is_partition n P) (r : ℕ × ℕ × ℕ × ℕ) (hr : r ∈ P) :
    r.2.1 ≤ n ∧ r.2.2.2 ≤ n ∧
    0 < mondrian_rect_width r ∧ 0 < mondrian_rect_height r ∧
    mondrian_rect_width r ≤ n ∧ mondrian_rect_height r ≤ n := by
  obtain ⟨hx, hy⟩ := h.2.1 r hr
  have hm : (r.2.1 - 1, r.2.2.2 - 1) ∈ mondrian_rect_cells r := by
    simp only [mondrian_rect_cells, Finset.mem_product, Finset.mem_Ico]
    omega
  have hu : (r.2.1 - 1, r.2.2.2 - 1) ∈
      P.toFinset.biUnion mondrian_rect_cells :=
    Finset.mem_biUnion.mpr ⟨r, List.mem_toFinset.mpr hr, hm⟩
  rw [h.2.2.2] at hu
  simp only [Finset.mem_product, Finset.mem_range] at hu
  dsimp [mondrian_rect_width, mondrian_rect_height]
  omega
