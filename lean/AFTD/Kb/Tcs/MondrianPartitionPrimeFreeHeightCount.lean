import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionPrimeFreeWidthCount
import AFTD.Kb.Tcs.MondrianPartitionSwap
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectSwap
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_partition_prime_free_height_count

Topic: combinatorics   Node: 341b003f9ece

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

For an admissible n-square partition into rectangles of one common positive integer area, and every prime p dividing n, the number of tiles whose height is not divisible by p is divisible by p.
-/

open scoped BigOperators

theorem mondrian_partition_prime_free_height_count (n p A : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : Nat.Prime p) (hpn : p ∣ n)
    (hApos : 0 < A) (hP : mondrian_is_partition n P)
    (hA : ∀ r ∈ P, mondrian_rect_area r = A) :
    p ∣ P.countP (fun r => decide (¬p ∣ mondrian_rect_height r)) := by
  have hswap := mondrian_partition_swap n P hP
  have hAswap : ∀ r ∈ P.map mondrian_rect_swap, mondrian_rect_area r = A := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    simpa only [mondrian_rect_area, mondrian_rect_width, mondrian_rect_height,
      mondrian_rect_swap, Nat.mul_comm] using hA s hs
  have hc := mondrian_partition_prime_free_width_count n p A (P.map mondrian_rect_swap)
    hp hpn hApos hswap hAswap
  rw [List.countP_map] at hc
  have heq : ((fun r => decide (¬p ∣ mondrian_rect_width r)) ∘ mondrian_rect_swap) =
      (fun r => decide (¬p ∣ mondrian_rect_height r)) := by
    funext r
    simp only [Function.comp_apply]
    apply decide_eq_decide.mpr
    rfl
  rw [heq] at hc
  exact hc
