import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionBounds
import AFTD.Kb.Tcs.MondrianPartitionPrimeFreeHeightCount
import AFTD.Kb.Tcs.MondrianPartitionPrimeFreeWidthCount
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_perfect_prime_free_side_counts

Topic: combinatorics   Node: 103c3ce6d24b

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

In any perfect admissible partition of an integer n-square, every prime p dividing n divides both the number of tiles with width not divisible by p and the number with height not divisible by p.
-/

open scoped BigOperators

theorem mondrian_perfect_prime_free_side_counts (n p : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : Nat.Prime p) (hpn : p ∣ n)
    (hP : mondrian_is_partition n P) (hz : mondrian_defect P = 0) :
    p ∣ P.countP (fun r => decide (¬p ∣ mondrian_rect_width r)) ∧
      p ∣ P.countP (fun r => decide (¬p ∣ mondrian_rect_height r)) := by
  cases P with
  | nil => simp
  | cons r P =>
    have hr : r ∈ r :: P := by simp
    have hb := mondrian_partition_bounds n (r :: P) hP r hr
    have hApos := Nat.mul_pos hb.2.2.1 hb.2.2.2.1
    have hA : ∀ s ∈ r :: P, mondrian_rect_area s = mondrian_rect_area r :=
      fun s hs => mondrian_defect_zero_equal (r :: P) hz s r hs hr
    exact ⟨mondrian_partition_prime_free_width_count n p (mondrian_rect_area r)
      (r :: P) hp hpn hApos hP hA,
      mondrian_partition_prime_free_height_count n p (mondrian_rect_area r)
      (r :: P) hp hpn hApos hP hA⟩
