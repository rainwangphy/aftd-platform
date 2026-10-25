import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectArea

/-!
# mondrian_cells_union_card

Topic: combinatorics   Node: f217c2554eaa

Provenance: helper lemma. arXiv:2610.19193, Section 1, and arXiv:2311.02385, Section 3 (available integer dimension pairs); helper for OP-280 and mondrian_no_perfect_partition.

For a list of rectangles with pairwise disjoint cell sets, the cardinality of their union equals the sum of their areas.
-/

theorem mondrian_cells_union_card (P : List (ℕ × ℕ × ℕ × ℕ))
    (h : P.Pairwise (fun r s =>
      Disjoint (mondrian_rect_cells r) (mondrian_rect_cells s))) :
    (P.toFinset.biUnion mondrian_rect_cells).card =
      (P.map mondrian_rect_area).sum := by
  induction P with
  | nil => simp
  | cons r P ih =>
    obtain ⟨hr, hP⟩ := List.pairwise_cons.mp h
    have hd : Disjoint (mondrian_rect_cells r)
        (P.toFinset.biUnion mondrian_rect_cells) := by
      rw [Finset.disjoint_biUnion_right]
      simpa only [List.mem_toFinset] using hr
    rw [List.toFinset_cons, Finset.biUnion_insert,
      Finset.card_union_of_disjoint hd, ih hP,
      List.map_cons, List.sum_cons]
    simp [mondrian_rect_cells, mondrian_rect_area,
      mondrian_rect_width, mondrian_rect_height]
