import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianLargePrimeCountNotDvd
import AFTD.Kb.Tcs.MondrianPartitionBounds
import AFTD.Kb.Tcs.MondrianPerfectAreaProduct
import AFTD.Kb.Tcs.MondrianPerfectPartitionDiv
import AFTD.Kb.Tcs.MondrianPrimePowerDvdSides
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectDiv
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianShapeBound
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_large_prime_descent

Topic: combinatorics   Node: 1c48a5466af8

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

If c is positive and p is a prime greater than c, any perfect partition of the c times p to the e square yields a perfect partition of the c-square.
-/

theorem mondrian_large_prime_descent (c p e : ℕ) (hc : 0 < c)
    (hp : Nat.Prime p) (hpc : c < p) :
    (∃ P, mondrian_is_partition (c * p ^ e) P ∧ mondrian_defect P = 0) →
      ∃ Q, mondrian_is_partition c Q ∧ mondrian_defect Q = 0 := by
  rintro ⟨P, hP, hz⟩
  cases P with
  | nil => have := hP.1; simp at this
  | cons r P =>
    have hr : r ∈ r :: P := by simp
    have hb := mondrian_partition_bounds (c * p ^ e) (r :: P) hP r hr
    have hA := Nat.mul_pos hb.2.2.1 hb.2.2.2.1
    have heq := mondrian_perfect_area_product (c * p ^ e) (r :: P) hP hz r hr
    have hcard := mondrian_shape_bound (c * p ^ e) (mondrian_rect_area r) (r :: P) hP
      (fun s hs => mondrian_defect_zero_equal (r :: P) hz s r hs hr)
    have hknot := mondrian_large_prime_count_not_dvd c p e (r :: P).length
      (mondrian_rect_area r) hc hp hpc (by have := hP.1; omega) hA heq hcard
    have hcop : (p ^ (2 * e)).Coprime (r :: P).length :=
      (hp.coprime_iff_not_dvd.mpr hknot).pow_left (2 * e)
    have hpowprod : p ^ (2 * e) ∣ (r :: P).length * mondrian_rect_area r := by
      rw [heq]
      have hnn : (c * p ^ e) ^ 2 = p ^ (2 * e) * c ^ 2 := by
        rw [Nat.mul_comm 2 e, pow_mul]
        ring
      rw [hnn]
      exact dvd_mul_right _ _
    have hpow := hcop.dvd_mul_left.mp hpowprod
    have hpc' : c < p := by nlinarith
    have hd : ∀ s ∈ r :: P, p ^ e ∣ mondrian_rect_width s ∧
        p ^ e ∣ mondrian_rect_height s := by
      intro s hs
      have hbs := mondrian_partition_bounds (c * p ^ e) (r :: P) hP s hs
      have hspow : p ^ (2 * e) ∣ mondrian_rect_area s := by
        rw [mondrian_defect_zero_equal (r :: P) hz s r hs hr]
        exact hpow
      exact mondrian_prime_power_dvd_sides c p e (mondrian_rect_width s)
        (mondrian_rect_height s) hp hpc' hbs.2.2.1 hbs.2.2.2.1
        hbs.2.2.2.2.1 hbs.2.2.2.2.2 hspow
    refine ⟨(r :: P).map (mondrian_rect_div (p ^ e)), ?_⟩
    exact mondrian_perfect_partition_div (p ^ e) c (pow_pos hp.pos e) (r :: P)
      (by simpa only [Nat.mul_comm] using hP) hz hd
