import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianDefectZeroOfEqual
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionSwap
import AFTD.Kb.Tcs.MondrianPartitionWidthDvdOfHeightTwoChains
import AFTD.Kb.Tcs.MondrianPrimeFreeHeightTwoChainEncoding
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectSwap
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_three_prime_common_area_sides_divide

Topic: combinatorics   Node: 6f14a3d462ec

Provenance: helper lemma. Helper for the three-prime extension of OP-280, arXiv:2610.19193 Section 1. This combines the width-free height cycle with the two superincreasing chains.

For primes p,q,r with p>r+1, if q divides the square side and every tile in a perfect admissible partition has area q^s*r*p^a, then q divides both dimensions of every tile.
-/

theorem mondrian_three_prime_common_area_sides_divide (n p q r a s : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) (hpr : r + 1 < p)
    (hP : mondrian_is_partition n P) (hz : mondrian_defect P = 0) (hqn : q ∣ n)
    (harea : ∀ u ∈ P, mondrian_rect_area u = q ^ s * r * p ^ a) :
    ∀ u ∈ P, q ∣ mondrian_rect_width u ∧ q ∣ mondrian_rect_height u := by
  have hpne : p ≠ r := by omega
  have hwidth : ∀ (Q : List (ℕ × ℕ × ℕ × ℕ)), mondrian_is_partition n Q →
      mondrian_defect Q = 0 →
      (∀ u ∈ Q, mondrian_rect_area u = q ^ s * r * p ^ a) →
      ∀ u ∈ Q, q ∣ mondrian_rect_width u := by
    intro Q hQ hQz hQA
    apply mondrian_partition_width_dvd_of_height_two_chains n q p r (q ^ s) Q hQ hQz hqn (pow_pos hq.pos s) hr.two_le hpr
    intro u hu hfree
    exact mondrian_prime_free_height_two_chain_encoding p q r a s (mondrian_rect_width u) (mondrian_rect_height u)
      hp hq hr hpne (hQA u hu) hfree
  have hw := hwidth P hP hz harea
  have hswapP := mondrian_partition_swap n P hP
  have hswapA : ∀ u ∈ P.map mondrian_rect_swap,
      mondrian_rect_area u = q ^ s * r * p ^ a := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    simpa only [mondrian_rect_area, mondrian_rect_width, mondrian_rect_height,
      mondrian_rect_swap, Nat.mul_comm] using harea v hv
  have hswapZ := mondrian_defect_zero_of_equal _ (q ^ s * r * p ^ a) hswapA
  have hh := hwidth (P.map mondrian_rect_swap) hswapP hswapZ hswapA
  intro u hu
  refine ⟨hw u hu, ?_⟩
  have hx := hh (mondrian_rect_swap u) (List.mem_map.mpr ⟨u, hu, rfl⟩)
  simpa only [mondrian_rect_width, mondrian_rect_height, mondrian_rect_swap] using hx
