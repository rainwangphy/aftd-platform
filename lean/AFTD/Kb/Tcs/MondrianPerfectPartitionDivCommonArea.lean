import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPerfectPartitionDiv
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectDiv
import AFTD.Kb.Tcs.MondrianRectDivDimensions
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_perfect_partition_div_common_area

Topic: combinatorics   Node: 8206576629b4

Provenance: helper lemma. For OP-280, arXiv:2610.19193, Section 1. Related work: arXiv:2007.09639, Theorem 4.1; HAL:hal-05729522v2, Lemma 2.3 (primitive cross sections and common-side descent). The periodic residue argument and the uniform two-prime common-area exclusion are developed here.

If q divides the square side and both dimensions of every tile in a perfect partition, and the common area is q^2 times B, coordinate division gives a perfect partition of the n/q square with common area B.
-/

theorem mondrian_perfect_partition_div_common_area (n q A B : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hq : 0 < q) (hqn : q ∣ n) (hP : mondrian_is_partition n P)
    (hz : mondrian_defect P = 0) (harea : ∀ r ∈ P, mondrian_rect_area r = A)
    (hAB : A = q ^ 2 * B)
    (hd : ∀ r ∈ P, q ∣ mondrian_rect_width r ∧ q ∣ mondrian_rect_height r) :
    ∃ Q, mondrian_is_partition (n / q) Q ∧ mondrian_defect Q = 0 ∧
      ∀ r ∈ Q, mondrian_rect_area r = B := by
  let Q := P.map (mondrian_rect_div q)
  have hP' : mondrian_is_partition (q * (n / q)) P := by
    simpa only [Nat.mul_div_cancel' hqn] using hP
  have hQ := mondrian_perfect_partition_div q (n / q) hq P hP' hz hd
  refine ⟨Q, hQ.1, hQ.2, ?_⟩
  intro r hr
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hw, hh⟩ := mondrian_rect_div_dimensions q hq s
    (hP.2.1 s hs).1 (hP.2.1 s hs).2 (hd s hs).1 (hd s hs).2
  apply Nat.eq_of_mul_eq_mul_left (pow_pos hq 2)
  calc
    q ^ 2 * mondrian_rect_area (mondrian_rect_div q s) = mondrian_rect_area s := by
      calc
        q ^ 2 * mondrian_rect_area (mondrian_rect_div q s) =
            (q * mondrian_rect_width (mondrian_rect_div q s)) *
            (q * mondrian_rect_height (mondrian_rect_div q s)) := by
          dsimp [mondrian_rect_area]
          ring
        _ = mondrian_rect_area s := by rw [hw, hh]; rfl
    _ = q ^ 2 * B := by rw [harea s hs, hAB]
