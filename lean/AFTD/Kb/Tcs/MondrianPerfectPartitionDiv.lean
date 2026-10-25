import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianDefectZeroOfEqual
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionDiv
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectDiv
import AFTD.Kb.Tcs.MondrianRectDivDimensions
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent

/-!
# mondrian_perfect_partition_div

Topic: combinatorics   Node: 4e0c5d893a63

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

Dividing coordinates by a preserves perfect admissible partitions when a is positive and divides every tile side.
-/

theorem mondrian_perfect_partition_div (a c : ℕ) (ha : 0 < a)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : mondrian_is_partition (a * c) P)
    (hz : mondrian_defect P = 0)
    (hd : ∀ r ∈ P, a ∣ mondrian_rect_width r ∧ a ∣ mondrian_rect_height r) :
    mondrian_is_partition c (P.map (mondrian_rect_div a)) ∧
      mondrian_defect (P.map (mondrian_rect_div a)) = 0 := by
  refine ⟨mondrian_partition_div a c ha P hp hd, ?_⟩
  have hscale : ∀ r ∈ P,
      a ^ 2 * mondrian_rect_area (mondrian_rect_div a r) = mondrian_rect_area r := by
    intro r hr
    obtain ⟨hw, hh⟩ := mondrian_rect_div_dimensions a ha r
      (hp.2.1 r hr).1 (hp.2.1 r hr).2 (hd r hr).1 (hd r hr).2
    calc
      a ^ 2 * mondrian_rect_area (mondrian_rect_div a r) =
          (a * mondrian_rect_width (mondrian_rect_div a r)) *
          (a * mondrian_rect_height (mondrian_rect_div a r)) := by
        dsimp [mondrian_rect_area]
        ring
      _ = mondrian_rect_area r := by rw [hw, hh]; rfl
  cases P with
  | nil => simp [mondrian_defect]
  | cons r P =>
    apply mondrian_defect_zero_of_equal _ (mondrian_rect_area (mondrian_rect_div a r))
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    apply Nat.eq_of_mul_eq_mul_left (pow_pos ha 2)
    rw [hscale t ht, hscale r (by simp)]
    exact mondrian_defect_zero_equal (r :: P) hz t r ht (by simp)
