import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectSwap
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_partition_swap

Topic: combinatorics   Node: 8a8209f46b28

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

Exchanging the x and y coordinate pairs of every rectangle preserves an admissible partition of the n-square.
-/

open scoped BigOperators

theorem mondrian_partition_swap (n : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hp : mondrian_is_partition n P) :
    mondrian_is_partition n (P.map mondrian_rect_swap) := by
  have hcell : ∀ r : ℕ × ℕ × ℕ × ℕ, ∀ x y : ℕ,
      (x, y) ∈ mondrian_rect_cells (mondrian_rect_swap r) ↔
        (y, x) ∈ mondrian_rect_cells r := by
    intro r x y
    simp only [mondrian_rect_swap, mondrian_rect_cells, Finset.mem_product, Finset.mem_Ico]
    tauto
  refine ⟨by simpa only [List.length_map] using hp.1, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact ⟨(hp.2.1 s hs).2, (hp.2.1 s hs).1⟩
  · rw [List.pairwise_map]
    apply hp.2.2.1.imp
    intro r s hrs
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ hr hs
      exact Finset.disjoint_left.mp hrs.1 ((hcell r x y).mp hr) ((hcell s x y).mp hs)
    · intro hc
      apply hrs.2
      simp only [mondrian_rect_congruent, mondrian_rect_width,
        mondrian_rect_height, mondrian_rect_swap] at hc ⊢
      tauto
  · ext ⟨x, y⟩
    constructor
    · intro h
      obtain ⟨r, hr, hc⟩ := Finset.mem_biUnion.mp h
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
      have hu : (y, x) ∈ P.toFinset.biUnion mondrian_rect_cells :=
        Finset.mem_biUnion.mpr ⟨s, List.mem_toFinset.mpr hs, (hcell s x y).mp hc⟩
      rw [hp.2.2.2] at hu
      simpa only [Finset.mem_product, Finset.mem_range, and_comm] using hu
    · intro h
      have hu : (y, x) ∈ Finset.range n ×ˢ Finset.range n := by
        simpa only [Finset.mem_product, Finset.mem_range, and_comm] using h
      rw [← hp.2.2.2] at hu
      obtain ⟨r, hr, hc⟩ := Finset.mem_biUnion.mp hu
      apply Finset.mem_biUnion.mpr
      exact ⟨mondrian_rect_swap r,
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, List.mem_toFinset.mp hr, rfl⟩),
        (hcell r x y).mpr hc⟩
