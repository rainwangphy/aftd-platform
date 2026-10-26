import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_cells_union_sum

Topic: combinatorics   Node: 750fee590358

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

Summing any integer-valued cell weight over a union of pairwise disjoint rectangle cell sets equals the sum of its sums over the rectangles.
-/

open scoped BigOperators

theorem mondrian_cells_union_sum (P : List (ℕ × ℕ × ℕ × ℕ))
    (h : P.Pairwise (fun r s =>
      Disjoint (mondrian_rect_cells r) (mondrian_rect_cells s)))
    (f : ℕ × ℕ → ℤ) :
    ∑ c ∈ P.toFinset.biUnion mondrian_rect_cells, f c =
      (P.map (fun r => ∑ c ∈ mondrian_rect_cells r, f c)).sum := by
  induction P with
  | nil => simp
  | cons r P ih =>
    obtain ⟨hr, hP⟩ := List.pairwise_cons.mp h
    have hd : Disjoint (mondrian_rect_cells r)
        (P.toFinset.biUnion mondrian_rect_cells) := by
      rw [Finset.disjoint_biUnion_right]
      simpa only [List.mem_toFinset] using hr
    rw [List.toFinset_cons, Finset.biUnion_insert, Finset.sum_union hd,
      ih hP, List.map_cons, List.sum_cons]
