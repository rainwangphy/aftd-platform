import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianDefectZeroOfEqual
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionSwap
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectSwap
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianTwoPrimeAreaWidthDvd

/-!
# mondrian_two_prime_area_sides_dvd

Topic: combinatorics   Node: 3e4c00bc6b31

Provenance: helper lemma. For OP-280, arXiv:2610.19193, Section 1. Related work: arXiv:2007.09639, Theorem 4.1; HAL:hal-05729522v2, Lemma 2.3 (primitive cross sections and common-side descent). The periodic residue argument and the uniform two-prime common-area exclusion are developed here.

For a perfect admissible square partition with common area q^s*p^t and q dividing the square side, both dimensions of every tile are divisible by q.
-/

theorem mondrian_two_prime_area_sides_dvd (n p q s t : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hP : mondrian_is_partition n P) (hz : mondrian_defect P = 0) (hqn : q ∣ n)
    (harea : ∀ r ∈ P, mondrian_rect_area r = q ^ s * p ^ t) :
    ∀ r ∈ P, q ∣ mondrian_rect_width r ∧ q ∣ mondrian_rect_height r := by
  have hw := mondrian_two_prime_area_width_dvd n p q s t P hp hq hP hz hqn harea
  have hswapP := mondrian_partition_swap n P hP
  have hswapA : ∀ r ∈ P.map mondrian_rect_swap,
      mondrian_rect_area r = q ^ s * p ^ t := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
    have hh := harea u hu
    simpa only [mondrian_rect_area, mondrian_rect_width, mondrian_rect_height,
      mondrian_rect_swap, Nat.mul_comm] using hh
  have hswapZ := mondrian_defect_zero_of_equal _ (q ^ s * p ^ t) hswapA
  have hh := mondrian_two_prime_area_width_dvd n p q s t (P.map mondrian_rect_swap)
    hp hq hswapP hswapZ hqn hswapA
  intro r hr
  refine ⟨hw r hr, ?_⟩
  have hx := hh (mondrian_rect_swap r) (List.mem_map.mpr ⟨r, hr, rfl⟩)
  simpa only [mondrian_rect_width, mondrian_rect_height, mondrian_rect_swap] using hx
