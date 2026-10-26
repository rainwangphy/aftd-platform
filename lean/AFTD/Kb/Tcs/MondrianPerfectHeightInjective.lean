import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionBounds
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent

/-!
# mondrian_perfect_height_injective

Topic: combinatorics   Node: c7b1f0e5185d

Provenance: helper lemma. For OP-280, arXiv:2610.19193, Section 1. Related work: arXiv:2007.09639, Theorem 4.1; HAL:hal-05729522v2, Lemma 2.3 (primitive cross sections and common-side descent). The periodic residue argument and the uniform two-prime common-area exclusion are developed here.

The heights of the tiles in a perfect admissible square partition are pairwise distinct.
-/

theorem mondrian_perfect_height_injective (n : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hP : mondrian_is_partition n P) (hz : mondrian_defect P = 0) :
    ∀ r ∈ P, ∀ s ∈ P, mondrian_rect_height r = mondrian_rect_height s → r = s := by
  have hpw : P.Pairwise (fun r s => mondrian_rect_height r ≠ mondrian_rect_height s) := by
    apply hP.2.2.1.imp_of_mem
    intro r s hr hs hrs he
    have harea := mondrian_defect_zero_equal P hz r s hr hs
    have hb := mondrian_partition_bounds n P hP r hr
    have hw : mondrian_rect_width r = mondrian_rect_width s := by
      dsimp [mondrian_rect_area] at harea
      rw [← he] at harea
      exact Nat.eq_of_mul_eq_mul_right hb.2.2.2.1 harea
    exact hrs.2 (Or.inl ⟨hw, he⟩)
  have hn : (P.map mondrian_rect_height).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact hpw
  intro r hr s hs he
  exact List.inj_on_of_nodup_map hn hr hs he
