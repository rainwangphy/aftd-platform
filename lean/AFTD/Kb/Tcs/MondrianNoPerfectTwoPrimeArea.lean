import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianNoPerfectPrimePowerArea
import AFTD.Kb.Tcs.MondrianPerfectAreaProduct
import AFTD.Kb.Tcs.MondrianPerfectPartitionDivCommonArea
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianTwoPrimeAreaSidesDvd
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_no_perfect_two_prime_area

Topic: combinatorics   Node: 547b0f3b8119

Provenance: original. Related work: For OP-280, arXiv:2610.19193, Section 1. Related work: arXiv:2007.09639, Theorem 4.1; HAL:hal-05729522v2, Lemma 2.3 (primitive cross sections and common-side descent). The periodic residue argument and the uniform two-prime common-area exclusion are developed here.

For any distinct primes p and q and natural exponents s and t, no perfect admissible partition of any integer square can have common tile area q^s*p^t.
-/

theorem mondrian_no_perfect_two_prime_area (p q s t n : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p ≠ q) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hP : mondrian_is_partition n P) (hz : mondrian_defect P = 0)
    (harea : ∀ r ∈ P, mondrian_rect_area r = q ^ s * p ^ t) : False := by
  induction s using Nat.strong_induction_on generalizing n P with
  | h s ih =>
    by_cases hs0 : s = 0
    · subst s
      exact mondrian_no_perfect_prime_power_area p t n hp P hP hz (by simpa using harea)
    obtain ⟨z, hzP⟩ : ∃ z, z ∈ P := by
      cases P with
      | nil => have := hP.1; simp at this
      | cons z P => exact ⟨z, by simp⟩
    have heq := mondrian_perfect_area_product n P hP hz z hzP
    rw [harea z hzP] at heq
    have hqn : q ∣ n := hq.dvd_of_dvd_pow (show q ∣ n ^ 2 by
      rw [← heq]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_pow_self q hs0) _) _)
    have hd := mondrian_two_prime_area_sides_dvd n p q s t P hp hq hP hz hqn harea
    have hqq : q ^ 2 ∣ q ^ s * p ^ t := by
      rw [← harea z hzP]
      simpa only [pow_two, mondrian_rect_area] using
        Nat.mul_dvd_mul (hd z hzP).1 (hd z hzP).2
    have hnot : ¬ q ∣ p := by
      intro hh
      rcases (Nat.dvd_prime hp).mp hh with hh | hh
      · exact hq.ne_one hh
      · exact hpq hh.symm
    have hcop : (q ^ 2).Coprime (p ^ t) :=
      ((hq.coprime_iff_not_dvd.mpr hnot).pow_right t).pow_left 2
    have hs2 : 2 ≤ s := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp (hcop.dvd_mul_right.mp hqq)
    have hsplit : q ^ s * p ^ t = q ^ 2 * (q ^ (s - 2) * p ^ t) := by
      have hh : q ^ s = q ^ 2 * q ^ (s - 2) := by rw [← pow_add]; congr 1; omega
      rw [hh, Nat.mul_assoc]
    obtain ⟨Q, hQP, hQZ, hQA⟩ := mondrian_perfect_partition_div_common_area n q (q ^ s * p ^ t)
      (q ^ (s - 2) * p ^ t) P hq.pos hqn hP hz harea hsplit hd
    exact ih (s - 2) (by omega) (n / q) Q hQP hQZ hQA
