import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StraightLineBisectionOfSideCardBounds
import AFTD.Kb.GameTheoryEconomics.StraightLine
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistent

/-!
# straight_line_bisection_of_cut_zero

Topic: fair_division   Node: 128d2c527634

Provenance: helper lemma. Boundary-assignment helper for planar_necklace_three_agents_three_cuts; arXiv:2610.27956 Proposition 9 and its bisection step. The definition permits arbitrary signs on zero cuts.

If every point lies on a given straight line and each of two colors has even size, that one line admits a consistent allocation bisecting both colors. This handles the collinear case using the permitted boundary signs.
-/

open Finset

theorem straight_line_bisection_of_cut_zero
    (P : Finset (ℝ × ℝ)) (c : (ℝ × ℝ) → Fin 2) (ℓ : StraightLine)
    (heven : ∀ j, 2 ∣ (P.filter fun p => c p = j).card)
    (hzero : ∀ p ∈ P, ℓ.cut p = 0) :
    ∃ α : (ℝ × ℝ) → Fin 2,
      is_straight_line_cut_consistent P {ℓ} α ∧
      ∀ i j : Fin 2,
        (P.filter fun p => α p = i ∧ c p = j).card =
          (P.filter fun p => c p = j).card / 2 := by
  apply straight_line_bisection_of_side_card_bounds P c ℓ heven
  · intro j
    have hempty : ((P.filter fun p => c p = j).filter fun p => 0 < ℓ.cut p) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro p hp
      rw [hzero p (mem_filter.mp hp).1]
      exact lt_irrefl _
    rw [hempty, card_empty]
    exact Nat.zero_le _
  · intro j
    have hempty : ((P.filter fun p => c p = j).filter fun p => ℓ.cut p < 0) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro p hp
      rw [hzero p (mem_filter.mp hp).1]
      exact lt_irrefl _
    rw [hempty, card_empty]
    exact Nat.zero_le _
