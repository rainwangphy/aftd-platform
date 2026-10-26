import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianListSumCountMod
import AFTD.Kb.Tcs.MondrianPartitionFloorMoment
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectFloorContribution
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent

/-!
# mondrian_partition_prime_free_width_count

Topic: combinatorics   Node: f59d1777d44a

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

For an admissible n-square partition into rectangles of one common positive integer area, and every prime p dividing n, the number of tiles whose width is not divisible by p is divisible by p.
-/

open scoped BigOperators

theorem mondrian_partition_prime_free_width_count (n p A : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : Nat.Prime p) (hpn : p ∣ n)
    (hApos : 0 < A) (hP : mondrian_is_partition n P)
    (hA : ∀ r ∈ P, mondrian_rect_area r = A) :
    p ∣ P.countP (fun r => decide (¬p ∣ mondrian_rect_width r)) := by
  let q := p ^ A.factorization p
  let u := A / q
  let f := fun r : ℕ × ℕ × ℕ × ℕ => (mondrian_rect_width r : ℤ) *
    (((r.2.2.2 / q : ℕ) : ℤ) - ((r.2.2.1 / q : ℕ) : ℤ))
  let pred := fun r : ℕ × ℕ × ℕ × ℕ => decide (¬p ∣ mondrian_rect_width r)
  have hq : 0 < q := pow_pos hp.pos _
  have hterm : ∀ r ∈ P, (p : ℤ) ∣ f r - if pred r then (u : ℤ) else 0 := by
    intro r hr
    by_cases hw : p ∣ mondrian_rect_width r
    · have hwZ : (p : ℤ) ∣ (mondrian_rect_width r : ℤ) := by exact_mod_cast hw
      simpa only [f, pred, hw, not_true_eq_false, decide_false, Bool.false_eq_true,
        if_false, sub_zero] using dvd_mul_of_dvd_left hwZ
          ((((r.2.2.2 / q : ℕ) : ℤ) - ((r.2.2.1 / q : ℕ) : ℤ)))
    · have hcop : q.Coprime (mondrian_rect_width r) :=
        (hp.coprime_iff_not_dvd.mpr hw).pow_left _
      have hqh : q ∣ mondrian_rect_height r := by
        apply hcop.dvd_mul_left.mp
        change q ∣ mondrian_rect_area r
        rw [hA r hr]
        exact Nat.ordProj_dvd A p
      have he := mondrian_rect_floor_contribution r
        (Nat.le_of_lt (hP.2.1 r hr).2) q hq hqh
      rw [hA r hr] at he
      simp only [f, pred, hw, not_false_eq_true, decide_true, if_true]
      change (p : ℤ) ∣ _ - (A / q : ℕ)
      rw [he]
      simp
  have hsum := mondrian_list_sum_count_mod P (p : ℤ) (u : ℤ) f pred hterm
  have hmoment := mondrian_partition_floor_moment n q P hP
  have hnZ : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hpn
  have hsumdiv : (p : ℤ) ∣ (P.map f).sum := by
    rw [show (P.map f).sum = (n : ℤ) * (n / q : ℕ) from hmoment]
    exact dvd_mul_of_dvd_left hnZ _
  have hprod : (p : ℤ) ∣ (P.countP pred : ℤ) * (u : ℤ) := by
    have hh := dvd_sub hsumdiv hsum
    have heq : (P.map f).sum - ((P.map f).sum - (P.countP pred : ℤ) * (u : ℤ)) =
        (P.countP pred : ℤ) * (u : ℤ) := by ring
    rwa [heq] at hh
  have hprodN : p ∣ P.countP pred * u := by exact_mod_cast hprod
  rcases hp.dvd_mul.mp hprodN with hc | hu
  · exact hc
  · exact (Nat.not_dvd_ordCompl hp (Nat.ne_of_gt hApos) hu).elim
