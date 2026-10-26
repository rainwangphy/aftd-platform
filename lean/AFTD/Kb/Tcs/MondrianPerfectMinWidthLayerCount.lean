import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianPartitionHorizontalMoment
import AFTD.Kb.Tcs.MondrianPartitionFloorMoment
import AFTD.Kb.Tcs.MondrianPartitionFloorMomentDivWidth
import AFTD.Kb.Tcs.MondrianCommonWidthDividesSide
import AFTD.Kb.Tcs.MondrianPerfectPrimeFreeSideCounts
import AFTD.Kb.Tcs.MondrianPerfectAreaProduct
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionBounds
import AFTD.Kb.Tcs.MondrianPartitionNormalizedPrimeFreeWidthMod
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_perfect_min_width_layer_count

Topic: combinatorics   Node: 273399cbfe40

Provenance: helper lemma. Next step of the modular inventory route for OP-280, arXiv:2610.19193, Section 1. The minimum-layer strengthening is derived here on paper and tested in experiments 5295 and 5296; it is not yet Lean-proved.

For a perfect admissible n-square partition and prime p dividing n, suppose b is the minimum p-adic exponent of tile widths. Then b is at most v_p(n), and the number of tiles in that minimum layer is congruent modulo p to the tile count if b=v_p(n), and to zero if b<v_p(n).
-/

theorem mondrian_perfect_min_width_layer_count (n p b : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : Nat.Prime p) (hpn : p ∣ n)
    (hP : mondrian_is_partition n P) (hz : mondrian_defect P = 0)
    (hmin : ∀ r ∈ P, p ^ b ∣ mondrian_rect_width r)
    (hex : ∃ r ∈ P, ¬ p ^ (b + 1) ∣ mondrian_rect_width r) :
    b ≤ n.factorization p ∧
      Nat.ModEq p (P.countP (fun r => decide (¬p ^ (b + 1) ∣ mondrian_rect_width r)))
        (if b = n.factorization p then P.length else 0) := by
  obtain ⟨z, hzP⟩ : ∃ z, z ∈ P := by
    cases P with
    | nil => have := hP.1; simp at this
    | cons z P => exact ⟨z, by simp⟩
  let d := p ^ b
  let A := mondrian_rect_area z
  let C := A / d
  let N := n / d
  let q := p ^ C.factorization p
  let u := C / q
  let k := P.length
  let cnt := P.countP (fun r => decide (¬ p ∣ mondrian_rect_width r / d))
  have hd : 0 < d := pow_pos hp.pos b
  have hzb := mondrian_partition_bounds n P hP z hzP
  have hn : 0 < n := hzb.2.2.1.trans_le hzb.2.2.2.2.1
  have hA : 0 < A := Nat.mul_pos hzb.2.2.1 hzb.2.2.2.1
  have hAd : d ∣ A := dvd_mul_of_dvd_left (hmin z hzP) _
  have hC : 0 < C := Nat.div_pos (Nat.le_of_dvd hA hAd) hd
  have hdn : d ∣ n := mondrian_common_width_divides_side n d P hP hmin
  have hbd : b ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)).mp hdn
  have hdC : d * C = A := Nat.mul_div_cancel' hAd
  have hdN : d * N = n := Nat.mul_div_cancel' hdn
  have harea : ∀ r ∈ P, (mondrian_rect_width r / d) * mondrian_rect_height r = C := by
    intro r hr
    apply Nat.eq_of_mul_eq_mul_left hd
    calc
      d * ((mondrian_rect_width r / d) * mondrian_rect_height r) = mondrian_rect_area r := by
        rw [← Nat.mul_assoc, Nat.mul_div_cancel' (hmin r hr)]
        rfl
      _ = A := mondrian_defect_zero_equal P hz r z hr hzP
      _ = d * C := hdC.symm
  have hmod := mondrian_partition_normalized_prime_free_width_mod n p d C P hp hd hP hmin harea
  change Nat.ModEq p (cnt * u) (N * (n / q)) at hmod
  have hunit : p.Coprime u := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_ordCompl hp (by omega : C ≠ 0))
  have hcount : cnt = P.countP (fun r => decide (¬ p ^ (b + 1) ∣ mondrian_rect_width r)) := by
    apply List.countP_congr
    intro r hr
    simp only [decide_eq_true_eq]
    apply not_congr
    have hw : d * (mondrian_rect_width r / d) = mondrian_rect_width r := Nat.mul_div_cancel' (hmin r hr)
    have he : p ^ (b + 1) = d * p := by rw [pow_succ]
    rw [he]
    conv_rhs => rw [← hw]
    exact (Nat.mul_dvd_mul_iff_left hd).symm
  refine ⟨hbd, ?_⟩
  rw [← hcount]
  by_cases hb : b = n.factorization p
  · rw [if_pos hb]
    have hNnot : ¬ p ∣ N := by
      simpa only [N, d, hb] using Nat.not_dvd_ordCompl hp (by omega : n ≠ 0)
    have hnorm : k * C = N * n := by
      apply Nat.eq_of_mul_eq_mul_left hd
      calc
        d * (k * C) = k * A := by rw [← hdC]; ring
        _ = n ^ 2 := mondrian_perfect_area_product n P hP hz z hzP
        _ = d * (N * n) := by rw [← hdN]; ring
    have hcop : q.Coprime N := (hp.coprime_iff_not_dvd.mpr hNnot).pow_left _
    have hqn : q ∣ n := hcop.dvd_mul_left.mp (by
      rw [← hnorm]
      exact dvd_mul_of_dvd_right (Nat.ordProj_dvd C p) k)
    have hqC : q * u = C := Nat.mul_div_cancel' (Nat.ordProj_dvd C p)
    have hqN : q * (n / q) = n := Nat.mul_div_cancel' hqn
    have hprod : k * u = N * (n / q) := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos (C.factorization p))
      calc
        q * (k * u) = k * C := by rw [← hqC]; ring
        _ = N * n := hnorm
        _ = N * (q * (n / q)) := congrArg (fun v => N * v) hqN.symm
        _ = q * (N * (n / q)) := by ring
    rw [← hprod] at hmod
    exact Nat.ModEq.cancel_right_of_coprime hunit hmod
  · rw [if_neg hb]
    have hba : b + 1 ≤ n.factorization p := by omega
    have hpow : p ^ (b + 1) ∣ n := (hp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)).mpr hba
    have hN : p ∣ N := by
      have hh : d * p ∣ d * N := by
        rw [hdN]
        simpa only [d, pow_succ] using hpow
      exact (Nat.mul_dvd_mul_iff_left hd).mp hh
    have hzero : Nat.ModEq p (N * (n / q)) (0 * u) := by
      simpa only [Nat.zero_mul] using (dvd_mul_of_dvd_left hN (n / q)).modEq_zero_nat
    exact Nat.ModEq.cancel_right_of_coprime hunit (hmod.trans hzero)
