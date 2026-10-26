import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionAreaOneImpossible
import AFTD.Kb.Tcs.MondrianPerfectAreaProduct
import AFTD.Kb.Tcs.MondrianPerfectPartitionDivCommonArea
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianTwoPrimeAreaSidesDvd
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_no_perfect_prime_power_area

Topic: combinatorics   Node: 3f7ef398b650

Provenance: helper lemma. For OP-280, arXiv:2610.19193, Section 1. Related work: arXiv:2007.09639, Theorem 4.1; HAL:hal-05729522v2, Lemma 2.3 (primitive cross sections and common-side descent). The periodic residue argument and the uniform two-prime common-area exclusion are developed here.

No perfect admissible partition of any integer square can have common tile area equal to a prime power p^t, including exponent zero.
-/

theorem mondrian_no_perfect_prime_power_area (p t n : ℕ) (hp : Nat.Prime p)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hP : mondrian_is_partition n P)
    (hz : mondrian_defect P = 0) (harea : ∀ r ∈ P, mondrian_rect_area r = p ^ t) : False := by
  induction t using Nat.strong_induction_on generalizing n P with
  | h t ih =>
    by_cases ht0 : t = 0
    · subst t
      exact mondrian_partition_area_one_impossible n P hP (by simpa using harea)
    obtain ⟨z, hzP⟩ : ∃ z, z ∈ P := by
      cases P with
      | nil => have := hP.1; simp at this
      | cons z P => exact ⟨z, by simp⟩
    have heq := mondrian_perfect_area_product n P hP hz z hzP
    rw [harea z hzP] at heq
    have hpn : p ∣ n := hp.dvd_of_dvd_pow (show p ∣ n ^ 2 by
      rw [← heq]
      exact dvd_mul_of_dvd_right (dvd_pow_self p ht0) _)
    have hd := mondrian_two_prime_area_sides_dvd n 2 p t 0 P Nat.prime_two hp hP hz hpn
      (by simpa using harea)
    have hpp : p ^ 2 ∣ p ^ t := by
      rw [← harea z hzP]
      simpa only [pow_two, mondrian_rect_area] using
        Nat.mul_dvd_mul (hd z hzP).1 (hd z hzP).2
    have ht2 : 2 ≤ t := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpp
    have hsplit : p ^ t = p ^ 2 * p ^ (t - 2) := by
      rw [← pow_add]
      congr 1
      omega
    obtain ⟨Q, hQP, hQZ, hQA⟩ := mondrian_perfect_partition_div_common_area n p (p ^ t) (p ^ (t - 2))
      P hp.pos hpn hP hz harea hsplit hd
    exact ih (t - 2) (by omega) (n / p) Q hQP hQZ hQA
