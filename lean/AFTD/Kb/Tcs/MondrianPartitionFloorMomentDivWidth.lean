import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianCommonWidthDividesSide
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionFloorMoment
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_partition_floor_moment_div_width

Topic: combinatorics   Node: 6e7e0cf618a7

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

If positive d divides every tile width in an admissible n-square partition, dividing all widths in the quotient-row moment by d gives (n/d) times floor(n/q).
-/

open scoped BigOperators

theorem mondrian_partition_floor_moment_div_width (n q d : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hdpos : 0 < d)
    (hP : mondrian_is_partition n P)
    (hd : ∀ r ∈ P, d ∣ mondrian_rect_width r) :
    (P.map (fun r => ((mondrian_rect_width r / d : ℕ) : ℤ) *
      (((r.2.2.2 / q : ℕ) : ℤ) - ((r.2.2.1 / q : ℕ) : ℤ)))).sum =
      ((n / d : ℕ) : ℤ) * ((n / q : ℕ) : ℤ) := by
  let F := fun r : ℕ × ℕ × ℕ × ℕ => ((mondrian_rect_width r / d : ℕ) : ℤ) *
    (((r.2.2.2 / q : ℕ) : ℤ) - ((r.2.2.1 / q : ℕ) : ℤ))
  let G := fun r : ℕ × ℕ × ℕ × ℕ => (mondrian_rect_width r : ℤ) *
    (((r.2.2.2 / q : ℕ) : ℤ) - ((r.2.2.1 / q : ℕ) : ℤ))
  have hmap : P.map (fun r => (d : ℤ) * F r) = P.map G := by
    apply List.map_congr_left
    intro r hr
    have hw : (d : ℤ) * ((mondrian_rect_width r / d : ℕ) : ℤ) =
        (mondrian_rect_width r : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' (hd r hr)
    change (d : ℤ) * (((mondrian_rect_width r / d : ℕ) : ℤ) *
      (((r.2.2.2 / q : ℕ) : ℤ) - ((r.2.2.1 / q : ℕ) : ℤ))) =
      (mondrian_rect_width r : ℤ) *
        (((r.2.2.2 / q : ℕ) : ℤ) - ((r.2.2.1 / q : ℕ) : ℤ))
    rw [← mul_assoc, hw]
  have hn : (d : ℤ) * ((n / d : ℕ) : ℤ) = (n : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (mondrian_common_width_divides_side n d P hP hd)
  change (P.map F).sum = _
  apply mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hdpos) : (d : ℤ) ≠ 0)
  calc
    (d : ℤ) * (P.map F).sum = (P.map G).sum := by
      rw [← List.sum_map_mul_left, hmap]
    _ = (n : ℤ) * ((n / q : ℕ) : ℤ) := mondrian_partition_floor_moment n q P hP
    _ = (d : ℤ) * (((n / d : ℕ) : ℤ) * ((n / q : ℕ) : ℤ)) := by
      rw [← hn]
      ring
