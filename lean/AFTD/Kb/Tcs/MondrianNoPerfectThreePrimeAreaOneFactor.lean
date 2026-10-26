import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianPartitionWidthDvdOfHeightTwoChains
import AFTD.Kb.Tcs.MondrianPrimeFreeHeightTwoChainEncoding
import AFTD.Kb.Tcs.MondrianNoPerfectTwoPrimeArea
import AFTD.Kb.Tcs.MondrianPerfectPartitionDivCommonArea
import AFTD.Kb.Tcs.MondrianPartitionSwap
import AFTD.Kb.Tcs.MondrianRectSwap
import AFTD.Kb.Tcs.MondrianDefectZeroOfEqual
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianPerfectAreaProduct
import AFTD.Kb.Tcs.MondrianPartitionBounds
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianThreePrimeCommonAreaSidesDivide
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianRectHeight

/-!
# mondrian_no_perfect_three_prime_area_one_factor

Topic: combinatorics   Node: 100270421601

Provenance: original. Related work: For the three-prime extension of OP-280, arXiv:2610.19193, Section 1. This develops the proved mondrian_no_perfect_two_prime_area and the width-free signed-height relation from this session.

For three distinct primes p,q,r with p>r+1, no perfect admissible integer square partition has common tile area q^s*r*p^a, for arbitrary natural a and s.
-/

theorem mondrian_no_perfect_three_prime_area_one_factor (p q r a s n : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : r + 1 < p)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hP : mondrian_is_partition n P)
    (hz : mondrian_defect P = 0)
    (harea : ∀ u ∈ P, mondrian_rect_area u = q ^ s * r * p ^ a) : False := by
  induction s using Nat.strong_induction_on generalizing n P with
  | h s ih =>
    by_cases hs0 : s = 0
    · subst s
      exact mondrian_no_perfect_two_prime_area p r 1 a n hp hr (by omega) P hP hz
        (by simpa only [pow_zero, one_mul, pow_one] using harea)
    obtain ⟨z, hzP⟩ : ∃ z, z ∈ P := by
      cases P with
      | nil => have := hP.1; simp at this
      | cons z P => exact ⟨z, by simp⟩
    have heq := mondrian_perfect_area_product n P hP hz z hzP
    rw [harea z hzP] at heq
    have hqn : q ∣ n := hq.dvd_of_dvd_pow (show q ∣ n ^ 2 by
      rw [← heq]
      exact dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self q hs0) _) _) _)
    have hd := mondrian_three_prime_common_area_sides_divide n p q r a s P hp hq hr hpr hP hz hqn harea
    have hqq : q ^ 2 ∣ q ^ s * (r * p ^ a) := by
      have hh : q ^ 2 ∣ mondrian_rect_area z := by
        simpa only [pow_two, mondrian_rect_area] using
          Nat.mul_dvd_mul (hd z hzP).1 (hd z hzP).2
      simpa only [harea z hzP, Nat.mul_assoc] using hh
    have hnotp : ¬ q ∣ p := by
      intro hh
      rcases (Nat.dvd_prime hp).mp hh with hh | hh
      · exact hq.ne_one hh
      · exact hpq hh.symm
    have hnotr : ¬ q ∣ r := by
      intro hh
      rcases (Nat.dvd_prime hr).mp hh with hh | hh
      · exact hq.ne_one hh
      · exact hqr hh
    have hcop : (q ^ 2).Coprime (r * p ^ a) :=
      (hq.coprime_iff_not_dvd.mpr (by
        intro hh
        rcases hq.dvd_mul.mp hh with hh | hh
        · exact hnotr hh
        · exact hnotp (hq.dvd_of_dvd_pow hh))).pow_left 2
    have hs2 : 2 ≤ s :=
      (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp (hcop.dvd_mul_right.mp hqq)
    have hsplit : q ^ s * r * p ^ a = q ^ 2 * (q ^ (s - 2) * r * p ^ a) := by
      have hh : q ^ s = q ^ 2 * q ^ (s - 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hh]
      ring
    obtain ⟨Q, hQP, hQZ, hQA⟩ := mondrian_perfect_partition_div_common_area n q
      (q ^ s * r * p ^ a) (q ^ (s - 2) * r * p ^ a) P hq.pos hqn hP hz harea hsplit hd
    exact ih (s - 2) (by omega) (n / q) Q hQP hQZ hQA
