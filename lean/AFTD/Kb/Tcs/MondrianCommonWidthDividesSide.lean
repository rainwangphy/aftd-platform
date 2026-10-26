import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianListSumCountMod
import AFTD.Kb.Tcs.MondrianPartitionHorizontalMoment
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_common_width_divides_side

Topic: combinatorics   Node: ec6fa54ae71c

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

Every common divisor of the tile widths in an admissible n-square partition divides n.
-/

open scoped BigOperators

theorem mondrian_common_width_divides_side (n d : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hP : mondrian_is_partition n P)
    (hd : ∀ r ∈ P, d ∣ mondrian_rect_width r) : d ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  let f : ℕ → ℤ := fun y => if y = 0 then 0 else 1
  let g := fun r : ℕ × ℕ × ℕ × ℕ =>
    (mondrian_rect_width r : ℤ) * (f r.2.2.2 - f r.2.2.1)
  have hdiv : (d : ℤ) ∣ (P.map g).sum := by
    have hs := mondrian_list_sum_count_mod P (d : ℤ) 0 g (fun _ => false) (by
      intro r hr
      have hw : (d : ℤ) ∣ (mondrian_rect_width r : ℤ) := by exact_mod_cast hd r hr
      simpa [g] using dvd_mul_of_dvd_left hw (f r.2.2.2 - f r.2.2.1))
    simpa using hs
  have he : (P.map g).sum = (n : ℤ) := by
    simpa [g, f, hn] using mondrian_partition_horizontal_moment n P hP f
  rw [he] at hdiv
  exact_mod_cast hdiv
